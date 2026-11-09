import os
import threading
import time
import html
from flask import Flask
import telebot
from telebot.types import InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup, KeyboardButton
import uuid
import re
import json
import base64
import hashlib
import tempfile
from datetime import datetime, timezone
try:  # only needed for the optional legacy Google Drive backup of the old SQLite file
    from google.oauth2 import service_account
    from googleapiclient.discovery import build
    from googleapiclient.http import MediaFileUpload
except ImportError:
    service_account = build = MediaFileUpload = None


def _load_dotenv(path=".env"):
    """Tiny .env reader (no extra dependency). Real environment variables always win."""
    try:
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))
    except FileNotFoundError:
        pass


_load_dotenv()

# ---- SMS gateway + Binance verification (PostgreSQL) live in payment_gateway.py / pgdb.py ----
# ---- embedded modules: the whole project is ONE file (pgdb + payment_gateway + SQL migrations) ----
import sys as _sys
import types as _types
_PGDB_SOURCE = r'''# -*- coding: utf-8 -*-
"""
pgdb.py - the ONE PostgreSQL access layer for bot.py and payment_gateway.py.

PostgreSQL (DATABASE_URL) is the single primary database. This module:
  * owns a psycopg3 connection pool (SSL aware, timeouts, retry on connect),
  * exposes a small sqlite3-shaped API (connect()/cursor()/execute()/commit()/rollback()/close(),
    rows indexable by position AND by column name, cursor.lastrowid/rowcount) so the existing
    bot handlers keep working unchanged,
  * translates the few SQLite-only SQL constructs the bot uses (? placeholders, INSERT OR IGNORE /
    OR REPLACE, AUTOINCREMENT, COLLATE NOCASE, CURRENT_TIMESTAMP, BEGIN IMMEDIATE, ...) into
    PostgreSQL SQL. All SQL stays parameterized,
  * runs versioned, idempotent, non-destructive SQL migrations (migrations/*.sql).

Nothing here ever prints DATABASE_URL or a password.
"""
import hashlib
import os
import re
import threading
import time
from decimal import Decimal

import psycopg
from psycopg import errors as pgerr
from psycopg.adapt import Dumper, Loader
from psycopg.pq import Format
from psycopg_pool import ConnectionPool

# --------------------------------------------------------------------------- exceptions
Error = psycopg.Error
IntegrityError = psycopg.IntegrityError
OperationalError = psycopg.OperationalError
UniqueViolation = pgerr.UniqueViolation

# --------------------------------------------------------------------------- type adaptation
# SQLite is loosely typed (an int can be compared with a TEXT column, a float stored in an INTEGER
# column, ...). The bot relies on that. We send int/float/bool parameters as *untyped* literals so
# PostgreSQL infers the type from the column/operator, exactly like SQLite would.


class _UntypedNumberDumper(Dumper):
    format = Format.TEXT
    oid = 0  # "unknown": the server resolves it from context

    def dump(self, obj):
        if isinstance(obj, bool):
            return b"1" if obj else b"0"
        return repr(obj).encode() if isinstance(obj, float) else str(obj).encode()


class _NumericLoader(Loader):
    """numeric -> int when integral text (e.g. SUM(bigint)), else float (balances/prices)."""
    format = Format.TEXT

    def load(self, data):
        s = bytes(data).decode()
        if "." not in s and "e" not in s.lower() and "n" not in s.lower():
            return int(s)
        return float(s)


def _configure(conn):
    ad = conn.adapters
    for t in (int, float, bool, Decimal):
        ad.register_dumper(t, _UntypedNumberDumper)
    ad.register_loader("numeric", _NumericLoader)


class Row(tuple):
    """sqlite3.Row look-alike: row[0], row['col'], dict(row), row.keys()."""

    def __new__(cls, values, names):
        obj = super().__new__(cls, values)
        obj._names = names
        return obj

    def keys(self):
        return list(self._names)

    def __getitem__(self, k):
        if isinstance(k, str):
            lk = k.lower()
            for i, n in enumerate(self._names):
                if n == lk:
                    return tuple.__getitem__(self, i)
            raise IndexError("No item with that key")
        return tuple.__getitem__(self, k)


def _row_factory(cursor):
    names = [c.name.lower() for c in (cursor.description or [])]

    def make(values):
        return Row(values, names)
    return make


# --------------------------------------------------------------------------- SQL translation
_UTC_NOW_TEXT = "to_char(timezone('UTC', now()), 'YYYY-MM-DD HH24:MI:SS')"
CONFLICT_KEYS = {"settings": "key"}  # INSERT OR REPLACE target columns (extend if you add tables)
_identity_cols = {}  # table -> identity/serial column name (for lastrowid)
_tr_cache = {}
_tr_lock = threading.Lock()


def _split_literals(sql):
    """-> list of (is_literal, text). Handles '' escapes. Double-quoted identifiers are kept as code."""
    parts, buf, i, n = [], [], 0, len(sql)
    while i < n:
        ch = sql[i]
        if ch == "'":
            if buf:
                parts.append((False, "".join(buf)))
                buf = []
            j = i + 1
            while j < n:
                if sql[j] == "'":
                    if j + 1 < n and sql[j + 1] == "'":
                        j += 2
                        continue
                    break
                j += 1
            parts.append((True, sql[i:j + 1]))
            i = j + 1
        else:
            buf.append(ch)
            i += 1
    if buf:
        parts.append((False, "".join(buf)))
    return parts


_RE_OR_IGNORE = re.compile(r"\bINSERT\s+OR\s+IGNORE\s+INTO\b", re.I)
_RE_OR_REPLACE = re.compile(r"\bINSERT\s+OR\s+REPLACE\s+INTO\s+(\w+)\s*\(([^)]*)\)", re.I)
_RE_AUTOINC = re.compile(r"\bINTEGER\s+PRIMARY\s+KEY\s+AUTOINCREMENT\b", re.I)
_RE_NOCASE = re.compile(r"([A-Za-z_][\w\.]*)\s+COLLATE\s+NOCASE\b", re.I)
_RE_ADDCOL = re.compile(r"\bADD\s+COLUMN\s+(?!IF\s+NOT\s+EXISTS)", re.I)
_RE_INTEGER = re.compile(r"\bINTEGER\b", re.I)
_RE_REAL = re.compile(r"\bREAL\b", re.I)
_RE_CURTS = re.compile(r"\bCURRENT_TIMESTAMP\b", re.I)
_RE_LIKE = re.compile(r"\bLIKE\b", re.I)
_RE_BEGIN = re.compile(r"^\s*BEGIN(\s+(IMMEDIATE|DEFERRED|EXCLUSIVE|TRANSACTION))*\s*;?\s*$", re.I)
_RE_PRAGMA = re.compile(r"^\s*PRAGMA\b", re.I)
_RE_INSERT_TABLE = re.compile(r"^\s*INSERT\s+(?:OR\s+\w+\s+)?INTO\s+(\w+)", re.I)


def translate(sql, with_params=True):
    """SQLite-flavoured SQL -> PostgreSQL. Returns (sql, meta)."""
    key = (sql, with_params)
    with _tr_lock:
        hit = _tr_cache.get(key)
    if hit:
        return hit
    meta = {"noop": False, "insert_table": None, "has_returning": False}
    if _RE_BEGIN.match(sql) or _RE_PRAGMA.match(sql):
        meta["noop"] = True
        res = ("", meta)
    else:
        is_ddl = bool(re.match(r"^\s*(CREATE|ALTER)\s+TABLE\b", sql, re.I))
        or_ignore = bool(_RE_OR_IGNORE.search(sql))
        replace_clause = ""
        m = _RE_OR_REPLACE.search(sql)
        if m:
            table, cols = m.group(1).lower(), [c.strip() for c in m.group(2).split(",")]
            target = CONFLICT_KEYS.get(table, cols[0])
            sets = [c for c in cols if c != target]
            replace_clause = (" ON CONFLICT (%s) DO UPDATE SET %s" % (target, ", ".join("%s=EXCLUDED.%s" % (c, c) for c in sets))
                              if sets else " ON CONFLICT DO NOTHING")
        out = []
        for is_lit, text in _split_literals(sql):
            if is_lit:
                out.append(text.replace("%", "%%") if with_params else text)
                continue
            t = text
            t = _RE_OR_IGNORE.sub("INSERT INTO", t)
            t = _RE_OR_REPLACE.sub(lambda mm: "INSERT INTO %s (%s)" % (mm.group(1), mm.group(2)), t)
            t = _RE_AUTOINC.sub("BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY", t)
            t = _RE_NOCASE.sub(lambda mm: "LOWER(%s)" % mm.group(1), t)
            t = _RE_CURTS.sub("(" + _UTC_NOW_TEXT + ")", t)
            t = _RE_LIKE.sub("ILIKE", t)  # SQLite LIKE is case-insensitive for ASCII
            if is_ddl:
                t = _RE_ADDCOL.sub("ADD COLUMN IF NOT EXISTS ", t)
                t = _RE_INTEGER.sub("BIGINT", t)
                t = _RE_REAL.sub("NUMERIC(18,4)", t)
            if with_params:
                t = t.replace("%", "%%").replace("?", "%s")
            out.append(t)
        s = "".join(out).rstrip().rstrip(";")
        if or_ignore:
            s += " ON CONFLICT DO NOTHING"
        elif replace_clause:
            s += replace_clause
        mi = _RE_INSERT_TABLE.match(s)
        if mi:
            meta["insert_table"] = mi.group(1).lower()
        meta["has_returning"] = bool(re.search(r"\bRETURNING\b", s, re.I))
        res = (s, meta)
    with _tr_lock:
        if len(_tr_cache) > 5000:
            _tr_cache.clear()
        _tr_cache[key] = res
    return res


def split_script(script):
    stmts, buf = [], []
    for is_lit, text in _split_literals(script):
        if is_lit:
            buf.append(text)
            continue
        text = re.sub(r"--[^\n]*", "", text)  # strip line comments (outside string literals)
        pieces = text.split(";")
        buf.append(pieces[0])
        for p in pieces[1:]:
            stmts.append("".join(buf).strip())
            buf = [p]
    stmts.append("".join(buf).strip())
    return [s for s in stmts if s]


# --------------------------------------------------------------------------- pool
_pool = None
_pool_lock = threading.Lock()


def _prepare_url(url):
    url = (url or "").strip()
    if url.startswith("postgres://"):
        url = "postgresql://" + url[len("postgres://"):]
    # Render's *external* hostnames require TLS; internal ones do not support/need it.
    if "sslmode=" not in url and re.search(r"\.render\.com|\.neon\.tech|\.supabase\.", url):
        url += ("&" if "?" in url else "?") + "sslmode=require"
    return url


def configured():
    return bool(os.environ.get("DATABASE_URL", "").strip())


def init(url=None, min_size=1, max_size=None):
    """Open the pool once. Safe to call repeatedly."""
    global _pool
    with _pool_lock:
        if _pool is not None:
            return _pool
        url = _prepare_url(url or os.environ.get("DATABASE_URL", ""))
        if not url:
            raise RuntimeError("DATABASE_URL is not set. PostgreSQL is the primary database; put it in .env.")
        max_size = max_size or int(os.environ.get("PG_POOL_MAX", "10"))
        pool = ConnectionPool(
            url, min_size=min_size, max_size=max_size, open=False, configure=_configure,
            check=ConnectionPool.check_connection, timeout=int(os.environ.get("PG_POOL_TIMEOUT", "30")),
            max_lifetime=1800, max_idle=300, name="botpool",
            kwargs={"autocommit": False, "row_factory": _row_factory, "connect_timeout": 10,
                    "application_name": "tgbot", "options": "-c statement_timeout=60000"},
        )
        pool.open(wait=True, timeout=int(os.environ.get("PG_CONNECT_WAIT", "30")))
        _pool = pool
        return pool


def close_pool():
    global _pool
    with _pool_lock:
        if _pool is not None:
            _pool.close()
            _pool = None


def _getconn():
    pool = init()
    last = None
    for attempt in range(3):  # transient connect errors only
        try:
            return pool.getconn()
        except (psycopg.OperationalError, Exception) as e:  # PoolTimeout is also retried once
            last = e
            time.sleep(0.5 * (attempt + 1))
    raise last


def health():
    """(ok, short text) - never includes credentials."""
    try:
        c = connect()
        try:
            v = c.execute("SHOW server_version").fetchone()[0]
        finally:
            c.close()
        return True, "PostgreSQL PRIMARY (server %s)" % v
    except Exception as e:
        return False, "PostgreSQL FAILED (%s)" % type(e).__name__


# --------------------------------------------------------------------------- sqlite-like objects
class Cursor:
    def __init__(self, conn):
        self._conn = conn
        self._cur = conn._raw.cursor()
        self.lastrowid = None

    # -- helpers
    def _identity(self, table):
        if table in _identity_cols:
            return _identity_cols[table]
        col = None
        try:
            r = self._conn._raw.execute(
                "SELECT column_name FROM information_schema.columns WHERE table_schema = current_schema() "
                "AND table_name = %s AND (is_identity = 'YES' OR column_default LIKE 'nextval(%%') "
                "ORDER BY ordinal_position LIMIT 1", (table,)).fetchone()
            col = r[0] if r else None
        except Exception:
            col = None
        if col is not None:  # only cache positives (a table may be created later in the same process)
            _identity_cols[table] = col
        return col

    def execute(self, sql, params=None):
        s, meta = translate(sql, params is not None)
        self.lastrowid = None
        if meta["noop"]:
            return self
        want_id = None
        if meta["insert_table"] and not meta["has_returning"]:
            idc = self._identity(meta["insert_table"])
            if idc:
                s = s + ' RETURNING "%s"' % idc
                want_id = idc
        self._cur.execute(s, params)
        if want_id and self._cur.description:
            row = self._cur.fetchone()
            self.lastrowid = row[0] if row else None
        return self

    def executemany(self, sql, seq):
        for p in seq:
            self.execute(sql, p)
        return self

    def executescript(self, script):
        for st in split_script(script):
            self.execute(st)
        self._conn.commit()
        return self

    def fetchone(self):
        return self._cur.fetchone() if self._cur.description else None

    def fetchall(self):
        return self._cur.fetchall() if self._cur.description else []

    def fetchmany(self, size=1):
        return self._cur.fetchmany(size) if self._cur.description else []

    def __iter__(self):
        return iter(self.fetchall())

    @property
    def rowcount(self):
        return self._cur.rowcount

    @property
    def description(self):
        return self._cur.description

    def close(self):
        try:
            self._cur.close()
        except Exception:
            pass


class Connection:
    """sqlite3.Connection look-alike backed by a pooled PostgreSQL connection."""

    def __init__(self):
        self._raw = _getconn()
        self._closed = False

    def cursor(self):
        return Cursor(self)

    def execute(self, sql, params=None):
        return self.cursor().execute(sql, params)

    def executescript(self, script):
        return self.cursor().executescript(script)

    def commit(self):
        self._raw.commit()

    def rollback(self):
        self._raw.rollback()

    def close(self):
        if self._closed:
            return
        self._closed = True
        raw, self._raw = self._raw, None
        try:
            if _pool is not None:
                try:
                    raw.rollback()  # anything not committed is discarded, like sqlite3
                except Exception:
                    pass
                _pool.putconn(raw)
        except Exception:
            pass

    def __enter__(self):
        return self

    def __exit__(self, et, ev, tb):
        if et is None:
            self.commit()
        else:
            self.rollback()
        return False

    def __del__(self):  # handlers that forget close() must not leak pool slots
        try:
            self.close()
        except Exception:
            pass


def connect():
    return Connection()


class Tx:
    """with Tx() as c: ...  -> one PostgreSQL transaction (commit on success, rollback on error)."""

    def __enter__(self):
        self.c = connect()
        return self.c

    def __exit__(self, et, ev, tb):
        try:
            if et is None:
                self.c.commit()
            else:
                self.c.rollback()
        finally:
            self.c.close()
        return False


# --------------------------------------------------------------------------- migrations
EMBEDDED_MIGRATIONS = None  # set by the single-file bot.py: {"001_baseline.sql": "...", ...}
_FORBIDDEN = re.compile(
    r"\b(DROP\s+DATABASE|DROP\s+SCHEMA|DROP\s+TABLE|TRUNCATE|DROP\s+COLUMN)\b|\bDELETE\s+FROM\s+\w+\s*;", re.I)


def apply_migrations(directory=None):
    """Apply migrations/*.sql in order, once each, under an advisory lock. Non-destructive only."""
    if directory is None and EMBEDDED_MIGRATIONS:
        bodies = dict(EMBEDDED_MIGRATIONS)          # single-file deployment: SQL is embedded in bot.py
    else:
        directory = directory or os.path.join(os.path.dirname(os.path.abspath(__file__)), "migrations")
        bodies = {}
        for f in sorted(x for x in os.listdir(directory) if x.endswith(".sql")):
            with open(os.path.join(directory, f), encoding="utf-8") as fh:
                bodies[f] = fh.read()
    files = sorted(bodies)
    applied_now = []
    raw = _getconn()
    try:
        raw.autocommit = True
        raw.execute("SELECT pg_advisory_lock(727274)")  # one migrator at a time (multi-instance safe)
        try:
            raw.execute("CREATE TABLE IF NOT EXISTS schema_migrations (version TEXT PRIMARY KEY, "
                        "checksum TEXT NOT NULL, applied_at TIMESTAMPTZ NOT NULL DEFAULT now())")
            done = {r[0]: r[1] for r in raw.execute("SELECT version, checksum FROM schema_migrations").fetchall()}
            for f in files:
                body = bodies[f]
                digest = hashlib.sha256(body.encode()).hexdigest()
                if f in done:
                    if done[f] != digest:
                        print("[migrations] WARNING: %s changed after it was applied (not re-run)." % f)
                    continue
                if _FORBIDDEN.search(re.sub(r"--[^\n]*", "", body)):
                    raise RuntimeError("migration %s contains a destructive statement; refusing to run it" % f)
                raw.autocommit = False
                try:
                    raw.execute(body)
                    raw.execute("INSERT INTO schema_migrations(version, checksum) VALUES (%s, %s)", (f, digest))
                    raw.commit()
                except Exception:
                    raw.rollback()
                    raise
                finally:
                    raw.autocommit = True
                applied_now.append(f)
        finally:
            raw.execute("SELECT pg_advisory_unlock(727274)")
    finally:
        try:
            raw.autocommit = False
            _pool.putconn(raw)
        except Exception:
            pass
    return applied_now


# --------------------------------------------------------------------------- single-instance polling lock
_lock_conn = None


def acquire_polling_lock(wait_seconds=90):
    """Cluster-wide guard (works across Render/VPS copies): only ONE process may poll Telegram.
    Holds a dedicated connection (outside the pool) for the process lifetime."""
    global _lock_conn
    url = _prepare_url(os.environ.get("DATABASE_URL", ""))
    deadline = time.time() + wait_seconds
    while True:
        c = psycopg.connect(url, autocommit=True, connect_timeout=10)
        ok = c.execute("SELECT pg_try_advisory_lock(727275)").fetchone()[0]
        if ok:
            _lock_conn = c
            return True
        c.close()
        if time.time() >= deadline:
            return False
        time.sleep(3)
'''
pgdb = _types.ModuleType("pgdb")
pgdb.__file__ = "pgdb(embedded)"
_sys.modules["pgdb"] = pgdb
exec(compile(_PGDB_SOURCE, "pgdb(embedded)", "exec"), pgdb.__dict__)
pgdb.EMBEDDED_MIGRATIONS = {
    "001_baseline.sql": r'''-- 001_baseline.sql : the bot's own tables, native PostgreSQL types.
-- Idempotent and NON-destructive: only CREATE ... IF NOT EXISTS / ADD COLUMN IF NOT EXISTS.
-- Money is NUMERIC (never binary floating point). Telegram ids are BIGINT.

CREATE TABLE IF NOT EXISTS users (
    user_id BIGINT PRIMARY KEY,
    first_name TEXT,
    balance NUMERIC(18,4) DEFAULT 0,
    username TEXT,
    referred_by BIGINT,
    referral_deposit_bonus NUMERIC(18,4) NOT NULL DEFAULT 0
);
ALTER TABLE users ADD COLUMN IF NOT EXISTS first_name TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS username TEXT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS referred_by BIGINT;
ALTER TABLE users ADD COLUMN IF NOT EXISTS referral_deposit_bonus NUMERIC(18,4) NOT NULL DEFAULT 0;

CREATE TABLE IF NOT EXISTS categories (
    cat_id TEXT PRIMARY KEY,
    name TEXT,
    price NUMERIC(18,4),
    has_emoji BIGINT DEFAULT 1,
    group_type TEXT DEFAULT 'mail',
    button_name TEXT,
    is_active BIGINT NOT NULL DEFAULT 1,
    created_at TEXT DEFAULT (to_char(timezone('UTC', now()), 'YYYY-MM-DD HH24:MI:SS'))
);

CREATE TABLE IF NOT EXISTS sub_services (
    sub_id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    cat_id TEXT,
    sub_name TEXT,
    price NUMERIC(18,4),
    has_emoji BIGINT DEFAULT 1
);

CREATE TABLE IF NOT EXISTS stock (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    cat_id TEXT,
    content TEXT,
    status TEXT NOT NULL DEFAULT 'available',
    sold_by BIGINT,
    sold_at TEXT,
    order_id TEXT
);

CREATE TABLE IF NOT EXISTS stock_sales (
    sale_id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    stock_id BIGINT NOT NULL UNIQUE,
    cat_id TEXT NOT NULL,
    category_name TEXT NOT NULL,
    button_name TEXT,
    buyer_user_id BIGINT NOT NULL,
    item_content TEXT NOT NULL,
    unit_price NUMERIC(18,4) NOT NULL,
    order_id TEXT NOT NULL,
    sold_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS referral_deposit_bonus_ledger (
    bonus_id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    deposit_request_id TEXT NOT NULL UNIQUE,
    referrer_id BIGINT NOT NULL,
    referred_user_id BIGINT NOT NULL,
    deposit_amount NUMERIC(18,4) NOT NULL,
    bonus_amount NUMERIC(18,4) NOT NULL DEFAULT 0.02,
    credited_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS custom_buttons (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    btn_name TEXT,
    btn_url TEXT
);

CREATE TABLE IF NOT EXISTS member_sell_orders (
    order_id TEXT PRIMARY KEY,
    user_id BIGINT NOT NULL,
    first_name TEXT,
    username TEXT,
    duration_key TEXT NOT NULL,
    duration_label TEXT NOT NULL,
    quantity BIGINT NOT NULL,
    price NUMERIC(18,4) NOT NULL,
    target_link TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'pending',
    created_at TEXT NOT NULL,
    completed_at TEXT,
    delivery_text TEXT,
    refunded_at TEXT
);

CREATE TABLE IF NOT EXISTS settings (
    key TEXT PRIMARY KEY,
    value TEXT
);

CREATE INDEX IF NOT EXISTS idx_member_sell_orders_user ON member_sell_orders(user_id, created_at);
CREATE INDEX IF NOT EXISTS idx_member_sell_orders_status ON member_sell_orders(status, created_at);
CREATE INDEX IF NOT EXISTS idx_stock_category_status_id ON stock(cat_id, status, id);
CREATE INDEX IF NOT EXISTS idx_stock_sales_category ON stock_sales(cat_id, sold_at);
CREATE INDEX IF NOT EXISTS idx_referral_bonus_referrer ON referral_deposit_bonus_ledger(referrer_id, credited_at);
CREATE INDEX IF NOT EXISTS idx_users_referred_by ON users(referred_by);
''',
    "002_payments_ledger.sql": r'''-- 002_payments_ledger.sql : SMS-gateway / Binance tables + append-only balance ledger.
-- Idempotent and NON-destructive.

CREATE TABLE IF NOT EXISTS pending_deposits (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    public_id TEXT NOT NULL UNIQUE,
    user_id BIGINT NOT NULL,
    username TEXT,
    full_name TEXT,
    provider TEXT NOT NULL,                  -- bkash|nagad|rocket|binance|binance_pay
    amount_minor BIGINT NOT NULL CHECK (amount_minor > 0),   -- BDT paisa credited to the user
    currency TEXT NOT NULL DEFAULT 'BDT',
    provider_trx_id TEXT NOT NULL,
    expected_foreign_minor BIGINT,           -- USD cents expected (binance)
    status TEXT NOT NULL DEFAULT 'PENDING'
        CHECK (status IN ('PENDING','PENDING_REVIEW','APPROVED','REJECTED','EXPIRED')),
    matched_payment_id BIGINT,
    review_reason TEXT,
    admin_notified BIGINT NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    expires_at TEXT
);
CREATE INDEX IF NOT EXISTS idx_pd_status ON pending_deposits(status);
CREATE INDEX IF NOT EXISTS idx_pd_trx ON pending_deposits(provider, provider_trx_id);
CREATE INDEX IF NOT EXISTS idx_pd_user ON pending_deposits(user_id);

CREATE TABLE IF NOT EXISTS payment_transactions (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    provider TEXT NOT NULL,
    provider_trx_id TEXT NOT NULL,
    amount_minor BIGINT NOT NULL,
    currency TEXT NOT NULL,
    merchant_id TEXT,
    device_id TEXT,
    reference TEXT,
    received_at TEXT,
    created_at TEXT NOT NULL,
    status TEXT NOT NULL CHECK (status IN
        ('RECEIVED','MATCHED','APPROVED','DUPLICATE','UNMATCHED','PENDING_REVIEW','REJECTED','FAILED')),
    status_reason TEXT,
    matched_deposit_id BIGINT,
    admin_alerted BIGINT NOT NULL DEFAULT 0,
    event_id TEXT,
    receiver_masked TEXT,
    receiver_verified BOOLEAN NOT NULL DEFAULT FALSE,
    UNIQUE (provider, provider_trx_id)       -- a provider transaction can exist exactly once
);
ALTER TABLE payment_transactions ADD COLUMN IF NOT EXISTS event_id TEXT;
ALTER TABLE payment_transactions ADD COLUMN IF NOT EXISTS receiver_masked TEXT;
ALTER TABLE payment_transactions ADD COLUMN IF NOT EXISTS receiver_verified BOOLEAN NOT NULL DEFAULT FALSE;
CREATE INDEX IF NOT EXISTS idx_pt_status ON payment_transactions(status);
CREATE INDEX IF NOT EXISTS idx_pt_created ON payment_transactions(created_at);
CREATE UNIQUE INDEX IF NOT EXISTS ux_pt_event_id ON payment_transactions(event_id) WHERE event_id IS NOT NULL;

CREATE TABLE IF NOT EXISTS payment_events (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    event_key TEXT NOT NULL UNIQUE,          -- idempotency / webhook replay protection
    source TEXT NOT NULL,
    event_type TEXT,
    payload_json TEXT,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS payment_settings (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS payment_audit_logs (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    ts TEXT NOT NULL, actor TEXT, action TEXT, ref TEXT, details TEXT
);
CREATE INDEX IF NOT EXISTS idx_pal_ref ON payment_audit_logs(ref);

CREATE TABLE IF NOT EXISTS api_devices (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    merchant_id TEXT NOT NULL,
    label TEXT,
    token_hash TEXT NOT NULL UNIQUE,         -- sha256 of the bearer token; the token itself is never stored
    is_active BIGINT NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL, last_seen_at TEXT, last_device_id TEXT, last_ip TEXT,
    consent_at TEXT, consent_version TEXT
);

CREATE TABLE IF NOT EXISTS binance_orders (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    merchant_trade_no TEXT NOT NULL UNIQUE,
    deposit_id BIGINT NOT NULL,
    user_id BIGINT NOT NULL,
    amount_usd TEXT NOT NULL, currency TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'INITIAL',
    prepay_id TEXT, checkout_url TEXT, qr_link TEXT, binance_ref TEXT,
    created_at TEXT NOT NULL, expires_at TEXT, paid_at TEXT
);

-- Foreign keys (deferrable: deposit <-> payment link each other inside one transaction).
-- NOT VALID so that any legacy row can never block start-up; new rows are always checked.
DO $$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'fk_pd_payment') THEN
    ALTER TABLE pending_deposits ADD CONSTRAINT fk_pd_payment FOREIGN KEY (matched_payment_id)
      REFERENCES payment_transactions(id) DEFERRABLE INITIALLY DEFERRED NOT VALID;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'fk_pt_deposit') THEN
    ALTER TABLE payment_transactions ADD CONSTRAINT fk_pt_deposit FOREIGN KEY (matched_deposit_id)
      REFERENCES pending_deposits(id) DEFERRABLE INITIALLY DEFERRED NOT VALID;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = 'fk_bo_deposit') THEN
    ALTER TABLE binance_orders ADD CONSTRAINT fk_bo_deposit FOREIGN KEY (deposit_id)
      REFERENCES pending_deposits(id) NOT VALID;
  END IF;
END $$;

-- DB-level guarantee: one provider transaction can be APPROVED for at most ONE deposit.
-- If legacy data already violates this the index is skipped with a WARNING (never blocks start-up).
DO $$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM pg_indexes WHERE indexname = 'ux_pd_trx_approved') THEN
    IF EXISTS (SELECT 1 FROM pending_deposits WHERE status = 'APPROVED'
               GROUP BY provider, provider_trx_id HAVING COUNT(*) > 1) THEN
      RAISE WARNING 'ux_pd_trx_approved NOT created: duplicate APPROVED provider_trx_id rows exist - review manually';
    ELSE
      CREATE UNIQUE INDEX ux_pd_trx_approved ON pending_deposits(provider, provider_trx_id) WHERE status = 'APPROVED';
    END IF;
  END IF;
END $$;

-- ---------------------------------------------------------------- append-only balance ledger
CREATE TABLE IF NOT EXISTS balance_ledger (
    id BIGINT GENERATED BY DEFAULT AS IDENTITY PRIMARY KEY,
    user_id BIGINT NOT NULL,
    delta NUMERIC(18,4) NOT NULL,
    balance_after NUMERIC(18,4) NOT NULL,
    reason TEXT NOT NULL DEFAULT 'balance_change',
    ref TEXT,                                  -- e.g. deposit:<public_id>  (unique => exactly-once credit)
    actor TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE INDEX IF NOT EXISTS ix_ledger_user ON balance_ledger(user_id, id);
CREATE UNIQUE INDEX IF NOT EXISTS ux_ledger_ref ON balance_ledger(ref) WHERE ref IS NOT NULL;

-- one-time opening entries for users that already hold a balance but have no ledger rows yet
INSERT INTO balance_ledger(user_id, delta, balance_after, reason, ref, actor)
SELECT u.user_id, u.balance, u.balance, 'opening_balance', 'opening:' || u.user_id, 'migration'
FROM users u
WHERE COALESCE(u.balance, 0) <> 0
  AND NOT EXISTS (SELECT 1 FROM balance_ledger l WHERE l.user_id = u.user_id)
ON CONFLICT DO NOTHING;

-- Every balance change (deposit, purchase, admin edit, refund, referral) is ledgered in the SAME
-- transaction as the users.balance update, so ledger and balance can never diverge.
CREATE OR REPLACE FUNCTION trg_users_balance_ledger() RETURNS trigger AS $f$
DECLARE d NUMERIC(18,4);
BEGIN
  IF TG_OP = 'INSERT' THEN
    d := COALESCE(NEW.balance, 0);
  ELSE
    d := COALESCE(NEW.balance, 0) - COALESCE(OLD.balance, 0);
  END IF;
  IF d = 0 THEN RETURN NEW; END IF;
  INSERT INTO balance_ledger(user_id, delta, balance_after, reason, ref, actor)
  VALUES (NEW.user_id, d, COALESCE(NEW.balance, 0),
          COALESCE(NULLIF(current_setting('app.ledger_reason', true), ''), 'balance_change'),
          NULLIF(current_setting('app.ledger_ref', true), ''),
          NULLIF(current_setting('app.ledger_actor', true), ''));
  RETURN NEW;
END $f$ LANGUAGE plpgsql;

DO $$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM pg_trigger WHERE tgname = 'users_balance_ledger') THEN
    CREATE TRIGGER users_balance_ledger AFTER INSERT OR UPDATE OF balance ON users
      FOR EACH ROW EXECUTE FUNCTION trg_users_balance_ledger();
  END IF;
END $$;

CREATE OR REPLACE VIEW ledger_reconciliation AS
SELECT u.user_id, COALESCE(u.balance, 0) AS balance, COALESCE(SUM(l.delta), 0) AS ledger_sum,
       COALESCE(u.balance, 0) - COALESCE(SUM(l.delta), 0) AS diff
FROM users u LEFT JOIN balance_ledger l ON l.user_id = u.user_id
GROUP BY u.user_id, u.balance;
''',
}
_PGW_SOURCE = r'''# -*- coding: utf-8 -*-
"""
payment_gateway.py  -  SMS Reader X gateway + Binance verification for bot.py   (PostgreSQL PRIMARY)

Design rules (the backend is the ONLY authority for deposits):
  * The Android app only reports "I saw this payment SMS". It never approves anything and never sees
    DATABASE_URL, Binance keys or the bot token.
  * Every approval happens inside ONE PostgreSQL transaction that also credits users.balance (and, via a
    trigger, appends to balance_ledger), so a deposit can never be credited twice or half-credited.
  * Exactly-once is enforced by the database itself: UNIQUE(provider, provider_trx_id), UNIQUE(event_id),
    UNIQUE ledger ref (deposit:<public_id>), a conditional PENDING->APPROVED UPDATE and row locks.
  * Notifications are sent only AFTER the transaction committed.
  * Secrets come from environment variables only.
"""
import base64
import hashlib
import hmac
import json
import os
import re
import secrets
import socket
import threading
import time
import uuid
from datetime import datetime, timezone, timedelta
from decimal import Decimal, ROUND_HALF_UP, InvalidOperation

import requests
import pgdb
from flask import Blueprint, request, jsonify

# --------------------------------------------------------------------------- config
_notify_user = lambda uid, text: None  # bot.py sets these
_notify_admin = lambda text, deposit_id=None: None

SUPPORTED_BD = {"bkash": "bKash", "nagad": "Nagad", "rocket": "Rocket"}
ACCEPTED_BINANCE_ASSETS = set(
    a.strip().upper() for a in os.environ.get("BINANCE_ACCEPTED_ASSETS", "USDT,USDC,FDUSD").split(",") if a.strip()
)
BDT_PER_USD = Decimal(os.environ.get("BINANCE_BDT_PER_USD", "125"))
UNMATCHED_ALERT_MIN = int(os.environ.get("UNMATCHED_ALERT_MINUTES", "15"))
DEPOSIT_ALERT_MIN = int(os.environ.get("DEPOSIT_ADMIN_ALERT_MINUTES", "10"))
BINANCE_HISTORY_GIVEUP_MIN = int(os.environ.get("BINANCE_HISTORY_GIVEUP_MINUTES", "30"))
RECONCILE_INTERVAL = int(os.environ.get("RECONCILE_INTERVAL_SECONDS", "20"))
REFERRAL_BONUS = 0.02  # identical to the existing bot.py admin-approval flow
# How the RECEIVING account is verified (see README_SMS_READER_X.md):
#   device (default) - the SMS can only reach the enrolled phone's SIM; the phone is authenticated by its
#                      server-issued Bearer token, and a receiving account is configured for the provider.
#                      SMS Reader X's "receiver_number" is the PAYER's number (a bKash/Nagad/Rocket
#                      "received" SMS never contains the receiver's own number), so it is NOT compared.
#   strict           - the client must send a receiver_number that equals a configured receiving number.
#   off              - no receiver check (not recommended).
RECEIVER_MODE = os.environ.get("GATEWAY_RECEIVER_MODE", "device").strip().lower()
if RECEIVER_MODE not in ("device", "strict", "off"):
    raise RuntimeError("GATEWAY_RECEIVER_MODE must be device, strict or off")
MAX_FUTURE_SKEW_MIN = int(os.environ.get("GATEWAY_MAX_FUTURE_SKEW_MINUTES", "15"))  # phone clocks drift

gateway_bp = Blueprint("sms_gateway", __name__)
_reconcile_state = {"last_run": None, "running": False, "last_error": None}


def configure(db_path=None, after_commit=None, notify_user=None, notify_admin=None):
    """db_path/after_commit are accepted for backward compatibility and ignored (PostgreSQL is primary)."""
    global _notify_user, _notify_admin
    if notify_user:
        _notify_user = notify_user
    if notify_admin:
        _notify_admin = notify_admin


# --------------------------------------------------------------------------- helpers
def utcnow():
    return datetime.now(timezone.utc)


def iso(dt=None):
    return (dt or utcnow()).strftime("%Y-%m-%dT%H:%M:%SZ")


def to_minor(value):
    """Decimal/str/number -> integer minor units (paisa / cents), exact."""
    d = Decimal(str(value)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    return int(d * 100)


def minor_str(minor):
    return f"{Decimal(minor) / 100:.2f}"


def _conn():
    """A pooled PostgreSQL connection. Caller must commit() writes and close()."""
    return pgdb.connect()


class _Tx:
    """One PostgreSQL transaction: COMMIT on success, ROLLBACK on error. Notify only after exit."""

    def __enter__(self):
        self.c = _conn()
        return self.c

    def __exit__(self, et, ev, tb):
        try:
            if et is None:
                self.c.commit()
            else:
                self.c.rollback()
        finally:
            self.c.close()
        return False


def audit(c, actor, action, ref="", details=""):
    # never put secrets / raw SMS here
    c.execute(
        "INSERT INTO payment_audit_logs(ts, actor, action, ref, details) VALUES (?,?,?,?,?)",
        (iso(), str(actor)[:80], action[:60], str(ref)[:80], str(details)[:500]),
    )


# --------------------------------------------------------------------------- schema
def init_schema():
    """Schema lives in migrations/*.sql (versioned, idempotent, non-destructive)."""
    return pgdb.apply_migrations()


def sha256_hex(s):
    return hashlib.sha256(s.encode()).hexdigest()


# --------------------------------------------------------------------------- devices / auth
def create_device(merchant_id, label="android"):
    """Returns the plaintext token ONCE. Only its hash is stored."""
    token = secrets.token_urlsafe(32)
    with _Tx() as c:
        c.execute(
            "INSERT INTO api_devices(merchant_id,label,token_hash,created_at) VALUES (?,?,?,?)",
            (merchant_id, label[:40], sha256_hex(token), iso()),
        )
        audit(c, "admin", "DEVICE_CREATED", merchant_id, label)
    return token


def bootstrap_device_from_env():
    token = os.environ.get("GATEWAY_BEARER_TOKEN", "").strip()
    merchant = os.environ.get("GATEWAY_MERCHANT_ID", "").strip()
    if not token or not merchant:
        return False
    if len(token) < 24:
        raise RuntimeError("GATEWAY_BEARER_TOKEN is too short (need >= 24 chars).")
    h = sha256_hex(token)
    with _Tx() as c:
        if not c.execute("SELECT 1 FROM api_devices WHERE token_hash=?", (h,)).fetchone():
            c.execute(
                "INSERT INTO api_devices(merchant_id,label,token_hash,created_at) VALUES (?,?,?,?)",
                (merchant, "env-bootstrap", h, iso()),
            )
            audit(c, "system", "DEVICE_BOOTSTRAPPED", merchant, "from environment")
    return True


_fail_log = {}  # ip -> [timestamps]


def _too_many_failures(ip):
    now = time.time()
    lst = [t for t in _fail_log.get(ip, []) if now - t < 300]
    _fail_log[ip] = lst
    return len(lst) >= 20


def _authenticate():
    """Returns device row or (None, response)."""
    ip = request.headers.get("X-Forwarded-For", request.remote_addr or "?").split(",")[0].strip()
    if _too_many_failures(ip):
        return None, (jsonify(error="rate_limited"), 429)
    hdr = request.headers.get("Authorization", "")
    if not hdr.startswith("Bearer ") or len(hdr) > 300:
        _fail_log.setdefault(ip, []).append(time.time())
        return None, (jsonify(error="unauthorized"), 401)
    given = sha256_hex(hdr[7:].strip())
    c = _conn()
    try:
        found = c.execute("SELECT * FROM api_devices WHERE token_hash=? AND is_active=1", (given,)).fetchone()
        if not found or not hmac.compare_digest(found["token_hash"], given):  # constant time
            c.rollback()
            _fail_log.setdefault(ip, []).append(time.time())
            return None, (jsonify(error="unauthorized"), 401)
        c.execute("UPDATE api_devices SET last_seen_at=?, last_ip=? WHERE id=?", (iso(), ip, found["id"]))
        c.commit()
        return found, None
    finally:
        c.close()


# --------------------------------------------------------------------------- core: approve / match
def _set_ledger_context(c, reason, ref, actor):
    """Transaction-local settings read by the balance_ledger trigger (same transaction, so atomic)."""
    c.execute("SELECT set_config('app.ledger_reason', ?, true), set_config('app.ledger_ref', ?, true), "
              "set_config('app.ledger_actor', ?, true)", (reason, ref, str(actor)[:60]))


def _credit_locked(c, dep, actor):
    """Atomically approve one deposit + credit balance. MUST run inside _Tx. Raises on race.
    Exactly-once is guaranteed by: conditional status UPDATE (row lock), UNIQUE ledger ref, and the
    partial UNIQUE index on APPROVED (provider, provider_trx_id)."""
    cur = c.execute(
        "UPDATE pending_deposits SET status='APPROVED', updated_at=? WHERE id=? AND status IN ('PENDING','PENDING_REVIEW')",
        (iso(), dep["id"]),
    )
    if cur.rowcount != 1:
        raise RuntimeError("deposit_not_pending")  # someone else approved it first -> abort, no credit
    amount_dec = Decimal(dep["amount_minor"]) / 100
    amount = float(amount_dec)
    _set_ledger_context(c, "deposit_credit", "deposit:" + dep["public_id"], actor)
    row = c.execute("SELECT referred_by FROM users WHERE user_id=? FOR UPDATE", (dep["user_id"],)).fetchone()
    referred_by = None
    if row is None:
        c.execute(
            "INSERT INTO users (user_id, first_name, balance, username, referred_by) VALUES (?,?,?,?,NULL) "
            "ON CONFLICT (user_id) DO UPDATE SET balance = COALESCE(users.balance,0) + EXCLUDED.balance",
            (dep["user_id"], dep["full_name"] or "User", amount_dec, dep["username"] or "N/A"),
        )
    else:
        c.execute("UPDATE users SET balance = COALESCE(balance,0) + ? WHERE user_id=?", (amount_dec, dep["user_id"]))
        referred_by = row["referred_by"]
    bonus_target = None
    if referred_by:
        if c.execute("SELECT 1 FROM users WHERE user_id=?", (referred_by,)).fetchone():
            r = c.execute(
                "INSERT OR IGNORE INTO referral_deposit_bonus_ledger "
                "(deposit_request_id, referrer_id, referred_user_id, deposit_amount, bonus_amount, credited_at) "
                "VALUES (?,?,?,?,?,?)",
                ("gw" + dep["public_id"], referred_by, dep["user_id"], amount, REFERRAL_BONUS, iso()),
            )
            if r.rowcount > 0:
                _set_ledger_context(c, "referral_bonus", "referral:" + dep["public_id"], "gateway")
                c.execute(
                    "UPDATE users SET balance = COALESCE(balance,0) + ?, "
                    "referral_deposit_bonus = COALESCE(referral_deposit_bonus,0) + ? WHERE user_id=?",
                    (REFERRAL_BONUS, REFERRAL_BONUS, referred_by),
                )
                bonus_target = referred_by
    _set_ledger_context(c, "", "", "")
    audit(c, actor, "DEPOSIT_APPROVED", dep["public_id"], f"user={dep['user_id']} amount={minor_str(dep['amount_minor'])} {dep['provider']}")
    return {"user_id": dep["user_id"], "amount": amount, "provider": dep["provider"],
            "public_id": dep["public_id"], "referrer": bonus_target}


def _norm_bd_number(v):
    """Any BD mobile format (+8801.., 8801.., 01.., spaces/dashes) -> 01XXXXXXXXX, or '' if not a BD mobile."""
    d = re.sub(r"\D", "", str(v or ""))
    if d.startswith("880"):
        d = d[2:]
    if len(d) == 10 and d.startswith("1"):
        d = "0" + d
    return d if re.fullmatch(r"01\d{9}", d) else ""


def configured_receivers(provider):
    """Server-side authorised receiving numbers. ENV (<PROVIDER>_RECEIVER_NUMBER, comma separated) wins;
    otherwise the admin-managed `settings` row (<provider>_num) the bot already shows to users."""
    env = os.environ.get(provider.upper() + "_RECEIVER_NUMBER", "").strip()
    if env:
        return {n for n in (_norm_bd_number(x) for x in env.split(",")) if n}
    c = _conn()
    try:
        row = c.execute("SELECT value FROM settings WHERE key=?", (provider + "_num",)).fetchone()
    finally:
        c.close()
    return {n for n in (_norm_bd_number(x) for x in (row[0] if row and row[0] else "").split(",")) if n}


AUTO_APPROVE_WINDOW_MIN = int(os.environ.get("DEPOSIT_AUTO_APPROVE_WINDOW_MINUTES", "1440"))


def _evaluate_bd(c, tx):
    """Match one bKash/Nagad/Rocket payment_transactions row against pending deposits.
    Returns (status, reason, notifications). Never guesses: anything doubtful -> PENDING_REVIEW."""
    notes = []
    cands = c.execute(
        "SELECT * FROM pending_deposits WHERE provider=? AND provider_trx_id=? AND status IN ('PENDING','PENDING_REVIEW') "
        "ORDER BY id FOR UPDATE",
        (tx["provider"], tx["provider_trx_id"]),
    ).fetchall()
    if not cands:
        manual = c.execute(
            "SELECT * FROM pending_deposits WHERE provider=? AND provider_trx_id=? AND status='APPROVED' AND matched_payment_id IS NULL",
            (tx["provider"], tx["provider_trx_id"]),
        ).fetchone()
        if manual:
            c.execute("UPDATE pending_deposits SET matched_payment_id=? WHERE id=?", (tx["id"], manual["id"]))
            return "APPROVED", "deposit was already approved manually; no second credit", notes
        return "UNMATCHED", "no pending deposit with this TrxID", notes
    if len(cands) > 1:
        for d in cands:
            c.execute("UPDATE pending_deposits SET status='PENDING_REVIEW', review_reason=?, updated_at=? WHERE id=?",
                      ("several users submitted this TrxID", iso(), d["id"]))
        notes.append(("admin", f"⚠️ {len(cands)} users claim the same TrxID {tx['provider_trx_id']} ({tx['provider']}). Nobody was credited."))
        return "PENDING_REVIEW", "multiple claimants", notes
    dep = cands[0]

    def _review(reason):
        c.execute("UPDATE pending_deposits SET status='PENDING_REVIEW', review_reason=?, matched_payment_id=?, updated_at=? WHERE id=?",
                  (reason, tx["id"], iso(), dep["id"]))
        notes.append(("admin", f"⚠️ Payment {tx['provider_trx_id']} {reason} (user {dep['user_id']}).", dep["id"]))
        return "PENDING_REVIEW", reason, notes

    if tx["currency"] != "BDT" or tx["amount_minor"] != dep["amount_minor"]:
        return _review(f"amount mismatch: expected {minor_str(dep['amount_minor'])} got {minor_str(tx['amount_minor'])} {tx['currency']}")
    if RECEIVER_MODE != "off" and not tx["receiver_verified"]:
        return _review("receiving account not verified (see GATEWAY_RECEIVER_MODE)")
    now = iso()
    if dep["expires_at"] and dep["expires_at"] < now:
        return _review("deposit request expired before the payment arrived")
    if AUTO_APPROVE_WINDOW_MIN > 0 and dep["created_at"] < iso(utcnow() - timedelta(minutes=AUTO_APPROVE_WINDOW_MIN)):
        return _review("deposit request is older than the auto-approval window")
    res = _credit_locked(c, dep, "gateway")
    c.execute("UPDATE pending_deposits SET matched_payment_id=? WHERE id=?", (tx["id"], dep["id"]))
    notes.append(("user", dep["user_id"], res))
    notes.append(("admin_ok", dep, res))
    return "APPROVED", "exact match", notes


def _dispatch(notes):
    for n in notes:
        try:
            if n[0] == "user":
                _notify_user(n[1], _success_text(n[2]))
                if n[2].get("referrer"):
                    _notify_user(n[2]["referrer"], "🎁 রেফারেল ডিপোজিট বোনাস! আপনার মেইন ব্যালেন্সে 0.02 টাকা যোগ হয়েছে।")
            elif n[0] == "admin_ok":
                dep, res = n[1], n[2]
                _notify_admin(f"✅ Auto-approved: user {dep['user_id']} ({dep['username'] or 'N/A'}) ৳{res['amount']:.2f} via {dep['provider']} • {dep['provider_trx_id']}")
            elif n[0] == "admin":
                _notify_admin(n[1], n[2] if len(n) > 2 else None)
        except Exception as e:
            print(f"[gateway] notify failed: {e}")


def _success_text(res):
    return f"✅ আপনার ডিপোজিট সফল হয়েছে!\nআপনার একাউন্টে ৳{res['amount']:.2f} যোগ করা হয়েছে। এখন আপনি কেনাকাটা করতে পারেন।"


# --------------------------------------------------------------------------- SMS payment ingestion
TRX_RE = re.compile(r"^[A-Za-z0-9_-]{4,40}$")


def _mask_ref(ref):
    ref = (ref or "")[:40]
    if re.fullmatch(r"\+?\d{8,15}", ref):
        return ref[:3] + "****" + ref[-3:]
    return re.sub(r"[^A-Za-z0-9*+_-]", "", ref)


EVENT_RE = re.compile(r"^[A-Za-z0-9._:-]{8,64}$")


def validate_payment_payload(d):
    """Accepts the existing contract (provider / transaction_id / reference / merchant_id) AND the SMS Reader X
    contract (method / trx_id / receiver_number / event_id / device_id). Returns (clean, error)."""
    if not isinstance(d, dict):
        return None, "body must be a JSON object"
    provider = str(d.get("provider") or d.get("method") or "").strip().lower()
    if provider not in SUPPORTED_BD:
        return None, "unsupported provider"
    trx = str(d.get("transaction_id") or d.get("trx_id") or "").strip().upper()
    if not TRX_RE.match(trx):
        return None, "invalid transaction_id"
    try:
        amt = Decimal(str(d.get("amount")))
        if not amt.is_finite() or amt <= 0 or amt > Decimal("1000000") or amt != amt.quantize(Decimal("0.01")):
            raise InvalidOperation
    except (InvalidOperation, ValueError):
        return None, "invalid amount"
    cur = str(d.get("currency", "BDT")).strip().upper()
    if cur != "BDT":
        return None, "unsupported currency"
    recv = str(d.get("received_at", ""))[:40]
    try:
        ts = datetime.fromisoformat(recv.replace("Z", "+00:00"))
        if ts.tzinfo is None:
            ts = ts.replace(tzinfo=timezone.utc)
    except ValueError:
        return None, "invalid received_at"
    if ts > utcnow() + timedelta(minutes=MAX_FUTURE_SKEW_MIN):
        return None, "received_at is in the future"
    event_id = str(d.get("event_id", "")).strip()
    if event_id and not EVENT_RE.match(event_id):
        return None, "invalid event_id"
    receiver = ""
    if d.get("receiver_number") not in (None, ""):
        receiver = _norm_bd_number(d.get("receiver_number"))
        if not receiver:
            return None, "invalid receiver_number"
    # NOTE: any client-sent "status"/"approved" field is ignored on purpose: only the backend approves.
    return {"provider": provider, "trx": trx, "amount_minor": to_minor(amt), "currency": cur,
            "reference": _mask_ref(str(d.get("reference", ""))), "received_at": recv,
            "merchant_id": str(d.get("merchant_id", ""))[:60], "device_id": str(d.get("device_id", ""))[:60],
            "event_id": event_id or None, "receiver": receiver}, None


def _process_sms_payment_once(device, p):
    notes = []
    recv_ok, recv_reason = False, None
    allowed = configured_receivers(p["provider"]) if RECEIVER_MODE != "off" else set()
    if RECEIVER_MODE == "off":
        recv_ok = True
    elif RECEIVER_MODE == "device":
        recv_ok = bool(allowed)  # device is authenticated (token) and an account is configured for this provider
        if not recv_ok:
            recv_reason = "no receiving account is configured for this provider"
    elif p["receiver"]:  # strict
        recv_ok = p["receiver"] in allowed
        if not recv_ok:
            recv_reason = ("receiver number does not match the configured account" if allowed
                           else "no receiving account is configured for this provider")
    else:
        recv_reason = "receiver number missing"
    with _Tx() as c:
        existing = c.execute("SELECT * FROM payment_transactions WHERE provider=? AND provider_trx_id=?",
                             (p["provider"], p["trx"])).fetchone()
        if existing is None and p["event_id"]:
            ev = c.execute("SELECT 1 FROM payment_transactions WHERE event_id=?", (p["event_id"],)).fetchone()
            if ev:
                audit(c, device["merchant_id"], "EVENT_ID_REUSED", p["trx"], f"event={p['event_id']}")
                return 409, {"status": "REJECTED", "duplicate": False, "reason": "event_id already used for another transaction"}
        tx = None
        if existing is None:
            cur = c.execute(
                "INSERT INTO payment_transactions(provider,provider_trx_id,amount_minor,currency,merchant_id,device_id,"
                "reference,received_at,created_at,status,status_reason,event_id,receiver_masked,receiver_verified) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?) ON CONFLICT (provider, provider_trx_id) DO NOTHING",
                (p["provider"], p["trx"], p["amount_minor"], p["currency"], device["merchant_id"], p["device_id"],
                 p["reference"], p["received_at"], iso(), "RECEIVED", "received", p["event_id"],
                 _mask_ref(p["receiver"]) if p["receiver"] else None, recv_ok),
            )
            if cur.rowcount == 1:
                tx = c.execute("SELECT * FROM payment_transactions WHERE id=?", (cur.lastrowid,)).fetchone()
            else:  # a concurrent identical request won the race; its row is committed now
                existing = c.execute("SELECT * FROM payment_transactions WHERE provider=? AND provider_trx_id=?",
                                     (p["provider"], p["trx"])).fetchone()
        if existing is not None:
            same = existing["amount_minor"] == p["amount_minor"]
            audit(c, device["merchant_id"], "DUPLICATE_EVENT", p["trx"], f"same_amount={same} device={p['device_id']}")
            if not same:
                notes.append(("admin", f"🚨 Duplicate TrxID {p['trx']} ({p['provider']}) arrived with a DIFFERENT amount. Not credited."))
                body = {"status": "DUPLICATE", "duplicate": True, "reason": "transaction id already recorded with different amount"}
            else:  # idempotent: a retry gets the ORIGINAL result, never a second credit
                body = {"status": existing["status"], "duplicate": True, "reason": existing["status_reason"]}
            result = (200, body)
        else:
            if RECEIVER_MODE == "strict" and p["receiver"] and not recv_ok:
                notes.append(("admin", f"🚨 {p['provider']} payment {p['trx']} was received on {_mask_ref(p['receiver'])}, "
                                       f"which is not a configured receiving number. Not credited."))
            status, reason, more = _evaluate_bd(c, tx)
            notes += more
            if status in ("UNMATCHED",) and recv_reason:
                reason = reason + "; " + recv_reason
            c.execute("UPDATE payment_transactions SET status=?, status_reason=?, matched_deposit_id=("
                      "SELECT id FROM pending_deposits WHERE matched_payment_id=? ORDER BY id LIMIT 1) WHERE id=?",
                      (status, reason, tx["id"], tx["id"]))
            audit(c, device["merchant_id"], "PAYMENT_" + status, p["trx"], reason)
            result = (200, {"status": status, "duplicate": False, "reason": reason})
    _dispatch(notes)  # AFTER commit: a failed Telegram message can never undo or repeat a credit
    return result


def process_sms_payment(device, p):
    """p = validated payload. Returns (http_code, json_dict). Idempotent and safe under concurrency."""
    for attempt in range(3):
        try:
            return _process_sms_payment_once(device, p)
        except pgdb.IntegrityError:
            if attempt == 2:
                return 409, {"status": "FAILED", "duplicate": False, "reason": "conflict, please retry"}
            time.sleep(0.05 * (attempt + 1))
        except pgdb.OperationalError:
            return 503, {"status": "FAILED", "duplicate": False, "reason": "temporarily unavailable, please retry"}


def create_deposit(user_id, username, full_name, provider, amount_bdt, trx_id,
                   expected_foreign_minor=None, expires_minutes=None):
    """Persistent PENDING deposit. For bKash/Nagad/Rocket also re-checks SMS that arrived earlier."""
    provider = provider.lower()
    trx = str(trx_id).strip().upper()
    if not TRX_RE.match(trx):
        raise ValueError("invalid transaction id")
    notes = []
    pid = uuid.uuid4().hex[:10]
    with _Tx() as c:
        c.execute("SELECT pg_advisory_xact_lock(hashtext(?))", (provider + ":" + trx,))  # serialize same-TrxID creators
        dup = c.execute("SELECT status FROM pending_deposits WHERE provider=? AND provider_trx_id=? AND user_id=? "
                        "AND status IN ('PENDING','PENDING_REVIEW','APPROVED')", (provider, trx, user_id)).fetchone()
        if dup:
            raise ValueError("you already submitted this transaction id")
        used = c.execute("SELECT 1 FROM pending_deposits WHERE provider=? AND provider_trx_id=? AND status='APPROVED'",
                         (provider, trx)).fetchone()
        if used:
            raise ValueError("this transaction id was already used")
        exp = iso(utcnow() + timedelta(minutes=expires_minutes)) if expires_minutes else None
        cur = c.execute(
            "INSERT INTO pending_deposits(public_id,user_id,username,full_name,provider,amount_minor,provider_trx_id,"
            "expected_foreign_minor,status,created_at,updated_at,expires_at) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
            (pid, user_id, username, full_name, provider, to_minor(amount_bdt), trx, expected_foreign_minor,
             "PENDING", iso(), iso(), exp),
        )
        dep_id = cur.lastrowid
        audit(c, user_id, "DEPOSIT_CREATED", pid, f"{provider} {minor_str(to_minor(amount_bdt))} trx={trx}")
        status = "PENDING"
        if provider in SUPPORTED_BD:
            tx = c.execute("SELECT * FROM payment_transactions WHERE provider=? AND provider_trx_id=? "
                           "AND status IN ('UNMATCHED','PENDING_REVIEW')", (provider, trx)).fetchone()
            if tx:  # SMS arrived BEFORE the user typed the TrxID
                st, reason, notes = _evaluate_bd(c, tx)
                c.execute("UPDATE payment_transactions SET status=?, status_reason=?, matched_deposit_id=("
                          "SELECT id FROM pending_deposits WHERE matched_payment_id=? LIMIT 1) WHERE id=?",
                          (st, reason, tx["id"], tx["id"]))
                audit(c, "gateway", "LATE_MATCH_" + st, trx, reason)
                status = c.execute("SELECT status FROM pending_deposits WHERE id=?", (dep_id,)).fetchone()["status"]
    _dispatch(notes)
    return {"id": dep_id, "public_id": pid, "status": status}


# --------------------------------------------------------------------------- admin actions
def admin_approve(deposit_id, admin_id):
    notes = []
    try:
        with _Tx() as c:
            dep = c.execute("SELECT * FROM pending_deposits WHERE id=? FOR UPDATE", (deposit_id,)).fetchone()
            if not dep or dep["status"] not in ("PENDING", "PENDING_REVIEW"):
                return None
            res = _credit_locked(c, dep, f"admin:{admin_id}")
            c.execute("UPDATE payment_transactions SET status='APPROVED', status_reason='approved by admin', matched_deposit_id=? "
                      "WHERE provider=? AND provider_trx_id=? AND status IN ('UNMATCHED','PENDING_REVIEW')",
                      (dep["id"], dep["provider"], dep["provider_trx_id"]))
            notes.append(("user", dep["user_id"], res))
    except pgdb.IntegrityError:
        # the database refused a second APPROVED deposit for the same provider transaction: nothing was credited
        with _Tx() as c:
            audit(c, f"admin:{admin_id}", "APPROVE_BLOCKED_DUPLICATE", str(deposit_id), "provider transaction already approved")
        return None
    except RuntimeError:  # deposit_not_pending (lost a race)
        return None
    _dispatch([n for n in notes])
    return res


def admin_reject(deposit_id, admin_id, reason="rejected by admin"):
    with _Tx() as c:
        dep = c.execute("SELECT * FROM pending_deposits WHERE id=? FOR UPDATE", (deposit_id,)).fetchone()
        if not dep or dep["status"] not in ("PENDING", "PENDING_REVIEW"):
            return None
        c.execute("UPDATE pending_deposits SET status='REJECTED', review_reason=?, updated_at=? WHERE id=?",
                  (reason, iso(), dep["id"]))
        c.execute("UPDATE payment_transactions SET status='REJECTED', status_reason=? WHERE provider=? AND provider_trx_id=? "
                  "AND status IN ('UNMATCHED','PENDING_REVIEW')", (reason, dep["provider"], dep["provider_trx_id"]))
        audit(c, f"admin:{admin_id}", "DEPOSIT_REJECTED", dep["public_id"], reason)
    return dict(dep)


def search_payments(query):
    """Admin search by Telegram user id or transaction id."""
    q = str(query).strip()
    c = _conn()
    try:
        if q.isdigit() and len(q) <= 12:
            rows = c.execute("SELECT * FROM pending_deposits WHERE user_id=? ORDER BY id DESC LIMIT 15", (int(q),)).fetchall()
        else:
            rows = c.execute("SELECT * FROM pending_deposits WHERE provider_trx_id=? ORDER BY id DESC LIMIT 15", (q.upper(),)).fetchall()
        out = [dict(r) for r in rows]
        txs = c.execute("SELECT * FROM payment_transactions WHERE provider_trx_id=? LIMIT 5", (q.upper(),)).fetchall()
        return out, [dict(t) for t in txs]
    finally:
        c.close()


def audit_history(ref, limit=15):
    c = _conn()
    try:
        return [dict(r) for r in c.execute(
            "SELECT * FROM payment_audit_logs WHERE ref=? ORDER BY id DESC LIMIT ?", (ref, limit))]
    finally:
        c.close()


def admin_stats():
    c = _conn()
    try:
        g = lambda sql, *a: c.execute(sql, a).fetchone()[0]
        return {
            "verified": g("SELECT COUNT(*) FROM pending_deposits WHERE status='APPROVED'"),
            "pending": g("SELECT COUNT(*) FROM pending_deposits WHERE status IN ('PENDING','PENDING_REVIEW')"),
            "failed": g("SELECT COUNT(*) FROM pending_deposits WHERE status IN ('REJECTED','EXPIRED')"),
            "unmatched": g("SELECT COUNT(*) FROM payment_transactions WHERE status='UNMATCHED'"),
            "review": g("SELECT COUNT(*) FROM payment_transactions WHERE status='PENDING_REVIEW'"),
            "dupes": g("SELECT COUNT(*) FROM payment_audit_logs WHERE action='DUPLICATE_EVENT'"),
            "devices": g("SELECT COUNT(*) FROM api_devices WHERE is_active=1"),
            "last_device_seen": (c.execute("SELECT MAX(last_seen_at) FROM api_devices").fetchone()[0]),
        }
    finally:
        c.close()


# --------------------------------------------------------------------------- Binance (a): Pay history by UID / API key
BINANCE_BASE_SAPI = os.environ.get("BINANCE_SAPI_BASE_URL", "https://api.binance.com")
_binance_lock = threading.Lock()
_binance_last_call = [0.0]


def _binance_keys():
    return os.environ.get("BINANCE_API_KEY", ""), os.environ.get("BINANCE_SECRET_KEY", "")


def binance_history_configured():
    k, s = _binance_keys()
    return bool(k and s)


def binance_fetch_history(start_ms, end_ms):
    """GET /sapi/v1/pay/transactions (read-only API key). Weight 3000 -> we throttle."""
    key, secret = _binance_keys()
    if not key or not secret:
        raise RuntimeError("BINANCE_API_KEY / BINANCE_SECRET_KEY not set")
    with _binance_lock:
        wait = 12 - (time.time() - _binance_last_call[0])
        if wait > 0:
            time.sleep(wait)
        _binance_last_call[0] = time.time()
    qs = f"startTime={int(start_ms)}&endTime={int(end_ms)}&limit=100&recvWindow=10000&timestamp={int(time.time()*1000)}"
    sig = hmac.new(secret.encode(), qs.encode(), hashlib.sha256).hexdigest()
    r = requests.get(f"{BINANCE_BASE_SAPI}/sapi/v1/pay/transactions?{qs}&signature={sig}",
                     headers={"X-MBX-APIKEY": key}, timeout=15)
    data = r.json()
    if r.status_code != 200 or str(data.get("code")) not in ("000000", "0", "200"):
        raise RuntimeError(f"binance history error http={r.status_code} code={data.get('code')} msg={str(data.get('msg') or data.get('message'))[:80]}")
    return data.get("data") or []


def binance_selftest():
    """Calls the history API once with the configured key. Returns (ok, human message)."""
    if not binance_history_configured():
        return False, "BINANCE_API_KEY / BINANCE_SECRET_KEY not set"
    try:
        recs = binance_fetch_history((time.time() - 3600) * 1000, time.time() * 1000)
        return True, f"OK - key works, {len(recs)} Pay transaction(s) in the last hour"
    except Exception as e:
        return False, str(e)


def _iso_to_ms(s):
    return int(datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp() * 1000)


def _safe_minor(v):
    try:
        return to_minor(v)
    except Exception:
        return 0


def _safe_time_iso(ms):
    try:
        return iso(datetime.fromtimestamp(int(ms) / 1000, timezone.utc))
    except Exception:
        return iso()


def _match_binance_record(c, dep, rec):
    """Pure check of one history record against one deposit. Returns (ok, reason).
    Anything incomplete/ambiguous is NOT approved (it goes to PENDING_REVIEW)."""
    for needed in ("transactionId", "transactionTime", "amount", "currency", "orderType"):
        if rec.get(needed) in (None, ""):
            return False, "incomplete record from Binance API"
    if str(rec.get("transactionId", "")).upper() != dep["provider_trx_id"]:
        return False, "id"
    if str(rec.get("orderType", "")).upper() not in ("C2C", "PAY"):
        return False, f"unsupported orderType {rec.get('orderType')}"
    try:
        amt = Decimal(str(rec.get("amount")))
    except InvalidOperation:
        return False, "bad amount"
    if amt <= 0:
        return False, "outgoing transaction"
    asset = str(rec.get("currency", "")).upper()
    if asset not in ACCEPTED_BINANCE_ASSETS:
        return False, f"asset {asset} not accepted"
    expected_uid = os.environ.get("BINANCE_UID", "").strip()
    rcv = rec.get("receiverInfo") or {}
    rcv_id = str(rcv.get("binanceId") or rcv.get("accountId") or "").strip()
    if expected_uid and rcv_id and rcv_id != expected_uid:
        return False, "payment was sent to a different Binance account"
    if int(rec.get("transactionTime", 0)) < _iso_to_ms(dep["created_at"]) - 10 * 60 * 1000:
        return False, "payment is older than this deposit request"
    if abs(amt - Decimal(dep["expected_foreign_minor"]) / 100) > Decimal("0.005"):
        return False, f"amount mismatch expected {minor_str(dep['expected_foreign_minor'])} got {amt}"
    return True, "ok"


_binance_reconcile_lock = threading.Lock()


def reconcile_binance_history():
    """One history fetch covers every pending Binance (UID) deposit. Returns number approved.
    Serialized in-process; cross-process safety comes from row locks + UNIQUE(provider, provider_trx_id)."""
    with _binance_reconcile_lock:
        return _reconcile_binance_history_locked()


def _reconcile_binance_history_locked():
    c = _conn()
    try:
        deps = c.execute("SELECT * FROM pending_deposits WHERE provider='binance' AND status='PENDING'").fetchall()
    finally:
        c.close()
    if not deps:
        return 0
    oldest = min(_iso_to_ms(d["created_at"]) for d in deps) - 15 * 60 * 1000
    recs = binance_fetch_history(oldest, int(time.time() * 1000))
    by_id = {str(r.get("transactionId", "")).upper(): r for r in recs}
    approved = 0
    for d in deps:
        rec = by_id.get(d["provider_trx_id"])
        notes = []
        with _Tx() as c:
            dep = c.execute("SELECT * FROM pending_deposits WHERE id=? FOR UPDATE", (d["id"],)).fetchone()
            if dep["status"] != "PENDING":
                continue
            if not rec:
                age_min = (utcnow() - datetime.fromisoformat(dep["created_at"].replace("Z", "+00:00"))).total_seconds() / 60
                if age_min > BINANCE_HISTORY_GIVEUP_MIN:
                    c.execute("UPDATE pending_deposits SET status='PENDING_REVIEW', review_reason=?, updated_at=? WHERE id=?",
                              ("payment not found in Binance Pay history", iso(), dep["id"]))
                    audit(c, "gateway", "BINANCE_NOT_FOUND", dep["public_id"], f"after {int(age_min)} min")
                    notes.append(("admin", f"⚠️ Binance deposit not found in Pay history: user {dep['user_id']} trx {dep['provider_trx_id']}", dep["id"]))
                _dispatch(notes)
                continue
            ok, why = _match_binance_record(c, dep, rec)
            dup = c.execute("SELECT 1 FROM payment_transactions WHERE provider='binance' AND provider_trx_id=?",
                            (dep["provider_trx_id"],)).fetchone()
            if dup:
                c.execute("UPDATE pending_deposits SET status='REJECTED', review_reason='transaction already used', updated_at=? WHERE id=?",
                          (iso(), dep["id"]))
                audit(c, "gateway", "BINANCE_DUPLICATE", dep["public_id"], dep["provider_trx_id"])
                notes.append(("admin", f"🚨 Duplicate Binance transaction {dep['provider_trx_id']} claimed by user {dep['user_id']}."))
                _dispatch(notes)
                continue
            cur = c.execute(
                "INSERT INTO payment_transactions(provider,provider_trx_id,amount_minor,currency,reference,received_at,created_at,status,status_reason) "
                "VALUES ('binance',?,?,?,?,?,?,?,?)",
                (dep["provider_trx_id"], _safe_minor(rec.get("amount")), str(rec.get("currency", ""))[:10],
                 str((rec.get("payerInfo") or {}).get("name", ""))[:40],
                 _safe_time_iso(rec.get("transactionTime")), iso(),
                 "PENDING_REVIEW" if not ok else "APPROVED", why))
            if ok:
                res = _credit_locked(c, dep, "binance-history")
                c.execute("UPDATE pending_deposits SET matched_payment_id=? WHERE id=?", (cur.lastrowid, dep["id"]))
                c.execute("UPDATE payment_transactions SET matched_deposit_id=? WHERE id=?", (dep["id"], cur.lastrowid))
                notes += [("user", dep["user_id"], res), ("admin_ok", dep, res)]
                approved += 1
            else:
                c.execute("UPDATE pending_deposits SET status='PENDING_REVIEW', review_reason=?, updated_at=? WHERE id=?",
                          (why, iso(), dep["id"]))
                audit(c, "gateway", "BINANCE_REVIEW", dep["public_id"], why)
                notes.append(("admin", f"⚠️ Binance deposit needs review: user {dep['user_id']} — {why}", dep["id"]))
        _dispatch(notes)
    return approved


# --------------------------------------------------------------------------- Binance (b): official Merchant API (orders)
def _merchant_cfg():
    return (os.environ.get("BINANCE_PAY_API_KEY", ""), os.environ.get("BINANCE_PAY_API_SECRET", ""),
            os.environ.get("BINANCE_PAY_BASE_URL", "https://bpay.binanceapi.com").rstrip("/"))


def merchant_configured():
    k, s, _ = _merchant_cfg()
    return bool(k and s)


def _merchant_post(path, body_obj):
    key, secret, base = _merchant_cfg()
    body = json.dumps(body_obj, separators=(",", ":"))
    ts = str(int(time.time() * 1000))
    nonce = secrets.token_hex(16)  # 32 chars
    payload = f"{ts}\n{nonce}\n{body}\n"
    sig = hmac.new(secret.encode(), payload.encode(), hashlib.sha512).hexdigest().upper()
    r = requests.post(base + path, data=body, timeout=15, headers={
        "Content-Type": "application/json", "BinancePay-Timestamp": ts, "BinancePay-Nonce": nonce,
        "BinancePay-Certificate-SN": key, "BinancePay-Signature": sig})
    return r.json()


def create_merchant_order(user_id, username, full_name, amount_bdt, ttl_minutes=15):
    usd = (Decimal(str(amount_bdt)) / BDT_PER_USD).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    if usd < Decimal("0.01"):
        raise ValueError("amount too small")
    mtn = uuid.uuid4().hex[:24].upper()  # merchantTradeNo: unique, alphanumeric <= 32
    expire_ms = int((time.time() + ttl_minutes * 60) * 1000)
    resp = _merchant_post("/binancepay/openapi/v2/order", {
        "env": {"terminalType": "APP"}, "merchantTradeNo": mtn, "orderAmount": float(usd), "currency": "USDT",
        "orderExpireTime": expire_ms,
        "goods": {"goodsType": "02", "goodsCategory": "Z000", "referenceGoodsId": "wallet-topup", "goodsName": "Wallet top-up"}})
    if resp.get("status") != "SUCCESS":
        with _Tx() as c:
            audit(c, "gateway", "BINANCE_ORDER_CREATE_FAILED", mtn, str(resp.get("code")) + ":" + str(resp.get("errorMessage"))[:100])
        raise RuntimeError(f"Binance Pay order failed: {resp.get('code')} {resp.get('errorMessage')}")
    d = resp["data"]
    dep = create_deposit(user_id, username, full_name, "binance_pay", amount_bdt, mtn,
                         expected_foreign_minor=to_minor(usd), expires_minutes=ttl_minutes)
    with _Tx() as c:
        c.execute("INSERT INTO binance_orders(merchant_trade_no,deposit_id,user_id,amount_usd,currency,status,prepay_id,"
                  "checkout_url,qr_link,created_at,expires_at) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                  (mtn, dep["id"], user_id, str(usd), "USDT", "INITIAL", d.get("prepayId"), d.get("checkoutUrl"),
                   d.get("qrcodeLink"), iso(), iso(datetime.fromtimestamp(expire_ms / 1000, timezone.utc))))
        audit(c, user_id, "BINANCE_ORDER_CREATED", mtn, f"usd={usd}")
    return {"merchantTradeNo": mtn, "usd": str(usd), "checkoutUrl": d.get("checkoutUrl"),
            "qrcodeLink": d.get("qrcodeLink"), "universalUrl": d.get("universalUrl"), "deposit_id": dep["id"]}


def _apply_paid_order(merchant_trade_no, paid_amount, paid_currency, binance_ref, source):
    """Single place that turns a PAID Binance order into a credit. Idempotent."""
    notes = []
    with _Tx() as c:
        o = c.execute("SELECT * FROM binance_orders WHERE merchant_trade_no=?", (merchant_trade_no,)).fetchone()
        if not o:
            return "unknown_order"
        dep = c.execute("SELECT * FROM pending_deposits WHERE id=? FOR UPDATE", (o["deposit_id"],)).fetchone()
        if dep["status"] == "APPROVED":
            return "already_approved"
        if dep["status"] not in ("PENDING", "PENDING_REVIEW"):
            audit(c, source, "BINANCE_PAID_AFTER_CLOSE", merchant_trade_no, dep["status"])
            notes.append(("admin", f"🚨 Binance order {merchant_trade_no} reported PAID but deposit is {dep['status']}. Check manually."))
            _after = "closed"
        else:
            exact = (str(paid_currency).upper() == o["currency"]) and (Decimal(str(paid_amount)) == Decimal(o["amount_usd"]))
            cur = c.execute("INSERT OR IGNORE INTO payment_transactions(provider,provider_trx_id,amount_minor,currency,reference,created_at,status,status_reason) "
                            "VALUES ('binance_pay',?,?,?,?,?,?,?)",
                            (merchant_trade_no, to_minor(paid_amount), str(paid_currency)[:10], str(binance_ref)[:40], iso(),
                             "APPROVED" if exact else "PENDING_REVIEW", "paid via " + source if exact else "amount/currency mismatch"))
            if cur.rowcount == 0:
                return "already_recorded"
            c.execute("UPDATE binance_orders SET status='PAID', paid_at=?, binance_ref=? WHERE id=?", (iso(), str(binance_ref)[:60], o["id"]))
            if exact:
                res = _credit_locked(c, dep, "binance-" + source)
                c.execute("UPDATE pending_deposits SET matched_payment_id=(SELECT id FROM payment_transactions WHERE provider='binance_pay' AND provider_trx_id=?) WHERE id=?",
                          (merchant_trade_no, dep["id"]))
                notes += [("user", dep["user_id"], res), ("admin_ok", dep, res)]
                _after = "approved"
            else:
                c.execute("UPDATE pending_deposits SET status='PENDING_REVIEW', review_reason='paid amount/currency differs from order', updated_at=? WHERE id=?", (iso(), dep["id"]))
                notes.append(("admin", f"⚠️ Binance order {merchant_trade_no}: paid {paid_amount} {paid_currency}, expected {o['amount_usd']} {o['currency']}.", dep["id"]))
                _after = "review"
    _dispatch(notes)
    return _after


def query_merchant_order(merchant_trade_no):
    resp = _merchant_post("/binancepay/openapi/v2/order/query", {"merchantTradeNo": merchant_trade_no})
    if resp.get("status") != "SUCCESS":
        return None
    return resp["data"]


def reconcile_merchant_orders():
    c = _conn()
    try:
        orders = c.execute("SELECT * FROM binance_orders WHERE status='INITIAL'").fetchall()
    finally:
        c.close()
    for o in orders:
        data = query_merchant_order(o["merchant_trade_no"])
        st = (data or {}).get("status")
        if st == "PAID":
            _apply_paid_order(o["merchant_trade_no"], data.get("orderAmount"), data.get("currency"),
                              data.get("transactionId") or data.get("prepayId") or "", "query")
        elif st in ("EXPIRED", "CANCELED", "ERROR") or o["expires_at"] < iso():
            new = st if st in ("EXPIRED", "CANCELED", "ERROR") else "EXPIRED"
            with _Tx() as c:
                c.execute("UPDATE binance_orders SET status=? WHERE id=? AND status='INITIAL'", (new, o["id"]))
                c.execute("UPDATE pending_deposits SET status='EXPIRED', updated_at=? WHERE id=? AND status='PENDING'", (iso(), o["deposit_id"]))
                audit(c, "gateway", "BINANCE_ORDER_" + new, o["merchant_trade_no"])
            _notify_user(o["user_id"], "⌛ Binance Pay অর্ডারের মেয়াদ শেষ হয়েছে। নতুন ডিপোজিট শুরু করুন।")


_cert_cache = {}


def _load_binance_cert(sn):
    if sn in _cert_cache:
        return _cert_cache[sn]
    resp = _merchant_post("/binancepay/openapi/certificates", {})
    for item in (resp.get("data") or []):
        _cert_cache[item["certSerial"]] = item["certPublic"]
    return _cert_cache.get(sn)


def verify_binance_webhook(headers, raw_body):
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import padding
    ts = headers.get("BinancePay-Timestamp", "")
    nonce = headers.get("BinancePay-Nonce", "")
    sig = headers.get("BinancePay-Signature", "")
    sn = headers.get("BinancePay-Certificate-SN", "")
    if not (ts and nonce and sig and sn) or not ts.isdigit():
        return False, "missing headers"
    if abs(time.time() * 1000 - int(ts)) > 5 * 60 * 1000:
        return False, "stale timestamp (replay protection)"
    pem = _load_binance_cert(sn)
    if not pem:
        return False, "unknown certificate"
    try:
        pub = serialization.load_pem_public_key(pem.encode())
        pub.verify(base64.b64decode(sig), f"{ts}\n{nonce}\n{raw_body.decode()}\n".encode(),
                   padding.PKCS1v15(), hashes.SHA256())
    except Exception:
        return False, "bad signature"
    return True, nonce


@gateway_bp.route("/binance/webhook", methods=["POST"])
def binance_webhook():
    raw = request.get_data(cache=False)[:20000]
    ok, info = verify_binance_webhook(request.headers, raw)
    if not ok:
        with _Tx() as c:
            audit(c, "binance-webhook", "WEBHOOK_REJECTED", "", info)
        _notify_admin(f"🚨 Binance webhook rejected: {info}")
        return jsonify(returnCode="FAIL", returnMessage=info), 400
    try:
        body = json.loads(raw)
        data = json.loads(body["data"]) if isinstance(body.get("data"), str) else (body.get("data") or {})
    except Exception:
        return jsonify(returnCode="FAIL", returnMessage="bad body"), 400
    key = f"binance:{body.get('bizIdStr') or body.get('bizId')}:{body.get('bizStatus')}"
    try:
        with _Tx() as c:
            c.execute("INSERT INTO payment_events(event_key,source,event_type,payload_json,created_at) VALUES (?,?,?,?,?)",
                      (key, "binance", body.get("bizStatus"), json.dumps({"merchantTradeNo": data.get("merchantTradeNo")}), iso()))
    except pgdb.IntegrityError:
        return jsonify(returnCode="SUCCESS", returnMessage=None)  # duplicate delivery: acknowledge, do nothing
    if body.get("bizType") == "PAY" and body.get("bizStatus") == "PAY_SUCCESS":
        # never trust the webhook alone: confirm through the signed query API
        q = query_merchant_order(data.get("merchantTradeNo", ""))
        if q and q.get("status") == "PAID":
            _apply_paid_order(data.get("merchantTradeNo"), q.get("orderAmount"), q.get("currency"),
                              q.get("transactionId") or body.get("bizIdStr") or "", "webhook")
    return jsonify(returnCode="SUCCESS", returnMessage=None)


# --------------------------------------------------------------------------- reconciler thread
def reconcile_once():
    if binance_history_configured():
        try:
            reconcile_binance_history()
        except Exception as e:
            print(f"[reconcile] binance history: {e}")
            _reconcile_state["last_error"] = str(e)[:120]
    if merchant_configured():
        try:
            reconcile_merchant_orders()
        except Exception as e:
            print(f"[reconcile] binance orders: {e}")
            _reconcile_state["last_error"] = str(e)[:120]
    cutoff_dep = iso(utcnow() - timedelta(minutes=DEPOSIT_ALERT_MIN))
    cutoff_tx = iso(utcnow() - timedelta(minutes=UNMATCHED_ALERT_MIN))
    notes = []
    with _Tx() as c:
        for d in c.execute("SELECT * FROM pending_deposits WHERE status IN ('PENDING','PENDING_REVIEW') "
                           "AND admin_notified=0 AND created_at<? AND provider IN ('bkash','nagad','rocket')", (cutoff_dep,)).fetchall():
            c.execute("UPDATE pending_deposits SET admin_notified=1 WHERE id=?", (d["id"],))
            notes.append(("admin", f"⏳ Deposit still unverified: user {d['user_id']} {d['username'] or ''} • {d['provider']} • ৳{minor_str(d['amount_minor'])} • TrxID {d['provider_trx_id']} • {d['review_reason'] or 'no matching SMS received'}", d["id"]))
        for t in c.execute("SELECT * FROM payment_transactions WHERE status='UNMATCHED' AND admin_alerted=0 AND created_at<?", (cutoff_tx,)).fetchall():
            c.execute("UPDATE payment_transactions SET admin_alerted=1 WHERE id=?", (t["id"],))
            notes.append(("admin", f"📭 Unmatched payment: {t['provider']} ৳{minor_str(t['amount_minor'])} TrxID {t['provider_trx_id']} (no user claimed it)"))
    _dispatch(notes)
    _reconcile_state["last_run"] = iso()


def start_reconciler():
    def loop():
        _reconcile_state["running"] = True
        while True:
            try:
                reconcile_once()
            except Exception as e:
                print(f"[reconcile] loop error: {e}")
                _reconcile_state["last_error"] = str(e)[:120]
            time.sleep(RECONCILE_INTERVAL)
    t = threading.Thread(target=loop, name="payment-reconciler", daemon=True)
    t.start()
    return t


def reconciler_status():
    return dict(_reconcile_state)


# --------------------------------------------------------------------------- HTTP API
@gateway_bp.route("/healthz", methods=["GET"])
def healthz():
    """Unauthenticated liveness probe for the hosting platform. Reveals no credentials/URLs."""
    ok, _ = pgdb.health()
    return jsonify(ok=ok), (200 if ok else 503)


@gateway_bp.route("/v1/health", methods=["GET"])
def v1_health():
    dev, err = _authenticate()
    if err:
        return err
    return jsonify(ok=True, service="sms-gateway", merchant_id=dev["merchant_id"], server_time=iso())


@gateway_bp.route("/v1/consent", methods=["POST"])
def v1_consent():
    dev, err = _authenticate()
    if err:
        return err
    d = request.get_json(silent=True) or {}
    if d.get("merchant_id") != dev["merchant_id"]:
        return jsonify(error="merchant_mismatch"), 403
    with _Tx() as c:
        c.execute("UPDATE api_devices SET consent_at=?, consent_version=? WHERE id=?",
                  (iso(), str(d.get("consent_version", "1"))[:20], dev["id"]))
        audit(c, dev["merchant_id"], "MERCHANT_CONSENT", str(d.get("device_id", ""))[:40], "accepted_at=" + str(d.get("accepted_at", ""))[:30])
    return jsonify(ok=True)


@gateway_bp.route("/v1/payments", methods=["POST"])
def v1_payments_post():
    dev, err = _authenticate()
    if err:
        return err
    if request.content_length and request.content_length > 4096:
        return jsonify(error="payload_too_large"), 413
    p, why = validate_payment_payload(request.get_json(silent=True))
    if not p:
        return jsonify(error="invalid_request", detail=why), 400
    if p["merchant_id"] and p["merchant_id"] != dev["merchant_id"]:
        return jsonify(error="merchant_mismatch"), 403
    c = _conn()
    try:
        c.execute("UPDATE api_devices SET last_device_id=? WHERE id=?", (p["device_id"], dev["id"]))
        c.commit()
    finally:
        c.close()
    code, body = process_sms_payment(dev, p)
    return jsonify(body), code


@gateway_bp.route("/v1/payments", methods=["GET"])
def v1_payments_get():
    dev, err = _authenticate()
    if err:
        return err
    status = request.args.get("status", "").upper()
    provider = request.args.get("provider", "").lower()
    q = request.args.get("q", "").strip().upper()[:40]
    date_from = request.args.get("from", "")[:10]
    date_to = request.args.get("to", "")[:10]
    raw_limit = request.args.get("limit", "100")
    limit = min(max(int(raw_limit), 1), 500) if raw_limit.isdigit() else 100
    sql = ("SELECT t.provider, t.provider_trx_id, t.amount_minor, t.currency, t.status, t.status_reason, t.received_at, t.created_at, "
           "d.user_id, d.username, d.full_name FROM payment_transactions t LEFT JOIN pending_deposits d ON d.id=t.matched_deposit_id "
           "WHERE t.merchant_id=?")
    args = [dev["merchant_id"]]
    if status in ("APPROVED", "REJECTED", "UNMATCHED", "PENDING_REVIEW"):
        sql += " AND t.status=?"; args.append(status)
    if provider in SUPPORTED_BD:
        sql += " AND t.provider=?"; args.append(provider)
    if q:
        sql += " AND t.provider_trx_id LIKE ?"; args.append("%" + re.sub(r"[^A-Z0-9_-]", "", q) + "%")
    if date_from:
        sql += " AND t.created_at>=?"; args.append(date_from)
    if date_to:
        sql += " AND t.created_at<=?"; args.append(date_to + "T23:59:59Z")
    sql += " ORDER BY t.id DESC LIMIT ?"; args.append(limit)
    c = _conn()
    try:
        rows = [{"provider": SUPPORTED_BD.get(r["provider"], r["provider"]), "transaction_id": r["provider_trx_id"],
                 "amount": minor_str(r["amount_minor"]), "currency": r["currency"], "status": r["status"],
                 "reason": r["status_reason"], "received_at": r["received_at"] or r["created_at"],
                 "telegram_user_id": r["user_id"], "telegram_username": r["username"], "telegram_full_name": r["full_name"]}
                for r in c.execute(sql, args)]
    finally:
        c.close()
    return jsonify(items=rows, count=len(rows))


@gateway_bp.route("/v1/stats", methods=["GET"])
def v1_stats():
    dev, err = _authenticate()
    if err:
        return err
    c = _conn()
    try:
        today = iso()[:10]
        rows = c.execute("SELECT provider, status, COUNT(*) n, SUM(amount_minor) s FROM payment_transactions WHERE merchant_id=? GROUP BY provider, status",
                         (dev["merchant_id"],)).fetchall()
        today_sum = c.execute("SELECT COALESCE(SUM(amount_minor),0) FROM payment_transactions WHERE merchant_id=? AND created_at>=?",
                              (dev["merchant_id"], today)).fetchone()[0]
        by_provider = {}
        for r in rows:
            bp = by_provider.setdefault(r["provider"], {"count": 0, "amount": 0})
            bp["count"] += r["n"]; bp["amount"] += r["s"] or 0
        by_status = {}
        for r in rows:
            by_status[r["status"]] = by_status.get(r["status"], 0) + r["n"]
        return jsonify(total=sum(by_status.values()), today_amount=minor_str(today_sum), by_status=by_status,
                       by_provider={k: {"count": v["count"], "amount": minor_str(v["amount"])} for k, v in by_provider.items()})
    finally:
        c.close()


# --------------------------------------------------------------------------- server start (real status, no fake "RUNNING")
def start_gateway_server(flask_app, host, port, tls_cert=None, tls_key=None):
    """Starts werkzeug in a thread, then proves it is listening. Returns (ok, detail)."""
    from werkzeug.serving import make_server
    ctx = None
    if tls_cert and tls_key:
        import ssl
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.load_cert_chain(tls_cert, tls_key)
    try:
        srv = make_server(host, port, flask_app, threaded=True, ssl_context=ctx)
    except (Exception, SystemExit) as e:  # werkzeug calls sys.exit(1) when the port is taken
        return False, f"{type(e).__name__}: port {port} could not be opened ({e}) - is another program using it?"
    threading.Thread(target=srv.serve_forever, name="sms-gateway-http", daemon=True).start()
    for _ in range(20):
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.5):
                return True, ("HTTPS" if ctx else "HTTP (no TLS)")
        except OSError:
            time.sleep(0.1)
    return False, "server thread started but port did not accept connections"
'''
pgw = _types.ModuleType("payment_gateway")
pgw.__file__ = "payment_gateway(embedded)"
_sys.modules["payment_gateway"] = pgw
exec(compile(_PGW_SOURCE, "payment_gateway(embedded)", "exec"), pgw.__dict__)
# ---- end embedded modules ----

# 🔑 টোকেন এবং অ্যাডমিন আইডি
TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
if not TOKEN:
    raise SystemExit("TELEGRAM_BOT_TOKEN is not set. Put it in .env (see .env.example). The old hardcoded token was exposed - create a new one in @BotFather.")
ADMIN_ID = int(os.environ.get("ADMIN_ID", "8465541252"))

FORCE_SUB_CHANNEL = "@Pro_Tools_Officials"

# ----------------- Flask App Initialization -----------------
app = Flask(__name__)

# ----------------- PostgreSQL is the ONLY primary database -----------------
# DATABASE_URL is backend-only (never given to the Android app, never printed, never logged).
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
if not DATABASE_URL:
    raise SystemExit("DATABASE_URL is not set. PostgreSQL is the primary database - put it in .env (see .env.example).")
try:
    pgdb.init(DATABASE_URL)
except Exception as _db_err:
    raise SystemExit(f"Cannot connect to PostgreSQL ({type(_db_err).__name__}). Check DATABASE_URL, network access and SSL.")


def db_connect(path=None, timeout=30):
    """Every handler still calls db_connect(...) exactly as before; it now returns a pooled PostgreSQL
    connection (sqlite3-compatible API: cursor/execute/commit/rollback/close, rows by index or name).
    `path`/`timeout` are accepted only for backward compatibility and are ignored."""
    return pgdb.connect()


# ----------------- Single-instance Telegram polling protection -----------------
# Prevent two copies of this bot (using the same token) from polling simultaneously
# on the same computer. The OS releases this lock automatically if Python exits.
_SINGLE_INSTANCE_LOCK_HANDLE = None


def acquire_single_instance_lock():
    global _SINGLE_INSTANCE_LOCK_HANDLE
    lock_name = "telegram_bot_polling_" + hashlib.sha256(TOKEN.encode("utf-8")).hexdigest()[:20] + ".lock"
    lock_path = os.path.join(tempfile.gettempdir(), lock_name)
    lock_handle = open(lock_path, "a+b")
    try:
        if os.name == "nt":
            import msvcrt
            lock_handle.seek(0, os.SEEK_END)
            if lock_handle.tell() == 0:
                lock_handle.write(b"0")
                lock_handle.flush()
            lock_handle.seek(0)
            msvcrt.locking(lock_handle.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except (OSError, BlockingIOError):
        lock_handle.close()
        print("ERROR: Another copy of this bot is already running on this computer. Stop the old bot process before starting this one.")
        return False

    _SINGLE_INSTANCE_LOCK_HANDLE = lock_handle
    return True


bot = telebot.TeleBot(TOKEN)
user_temp_deposit = {}
pending_deposits = {}
admin_states = {}
order_delivery_cache = {}
member_sell_states = {}  # Independent state; does not alter existing service flows.

# ----------------- Premium Custom Emoji Config (Buttons) -----------------
PREMIUM_EMOJIS = {
    "all_services": "5406683434124859552",
    "deposit": "5264895611517300926",
    "profile": "5325971446625758812",
    "support": "5269402556924180806",
    "restart": "6084506256427456298",
    "admin_panel": "6269458311381258421",
    "search_user": "5435907392334215552",

    "bkash": "6152327402098793153",
    "nagad": "6152331409303280461",
    "rocket": "6086803441160558654",
    "binance": "5798751138647905130",
    "bonus": "5321280470460145769",

    "money_10": "5879991085001871624",
    "money_20": "5879991085001871624",
    "money_30": "5879991085001871624",
    "money_40": "5879991085001871624",

    "get_code": "5042101437237036298",
    "referral": "5386380500946414098",

    "package_item": "5251680306385151250",
    "telegram_premium_cat": "5789911984283586269",
    "vpn_service_cat": "5998881947328188290",
    "mail_cat": "5354826222331245563",
    "proxy_cat": "5287292843763713628",
    "mail_item": "5967280668885913944",
    "proxy_item": "4956560549287560231",
    # Screenshot-specific service button emojis
    "mail_service_item": "5354826222331245563",
    "proxy_9_item": "6143321667427904097",
    "proxy_711_item": "6143393822878475954",
    "proxy_h143_item": "5375177250553487549",
    "proxy_rapid_item": "6143192522056283070",
    "proxy_loki_item": "6147909495658913509",
    "qty_select": "6071063305143719063",
    "back_button": "6206505206197261313",

    "channel_join": "6206505206197261313",
    "verify_tick": "6089184854497302293",

    "open_here_btn": "5368516976048104432",
    "txt_file_btn": "6109595432441090250",

    "vpn_express": "5796153709931009517",
    "vpn_cyberghost": "5796309230696797985",
    "vpn_panda": "5796561774773801876",
    "vpn_ipvanish": "5816862049367494010", 
    "vpn_nord": "5796345694969140339",
    "vpn_hma": "5796595022115639741",
    "vpn_pia": "5794298344188678751",
    "vpn_surfshark": "5796592771552777710",
    "vpn_bitdefender": "5793973558761756143",
    "vpn_turbo": "5796633857209931262",
    "vpn_proton": "5796504385420792898",

    "analytics": "5213107179329953547",
    "member_count_file": "5314665894406805639",
    "balance_list": "5215420556089776398",
    "download_txt": "5435932616677145539",
    "recover_balance": "6084506256427456298",
    "live_broadcast": "6219940267626078011",
    "add_balance": "6219646698021463224",
    "bulk_update": "6084506256427456298",
    "remove_money": "6068810023566317366",
    "post_edit": "5435907392334215552",
    "button_edit": "5406683434124859552",
    "edit_service": "5269402556924180806",
    "manage_stock": "5314665894406805639",
    "approve_btn": "6269285159774720688",
    "reject_btn": "6068810023566317366",
    "refresh_data": "6084506256427456298",
    "edit_pencil": "5435907392334215552",
    "delete_trash": "6068810023566317366"
}

POST_PREMIUM_EMOJIS = {
    "welcome_heart": "6292078018638651747",
    "welcome_shop": "5350699789551935589",
    "list_point": "6068777875736109056",
    "trusted_badge": "6084746478243288096",
    "fast_speed": "6088947729352890506",
    "down_arrow": "6219700471012009032",
    "warn_icon": "6068810023566317366",
    "step_tick": "6125147242731933920",
    "support_headphone": "6282996898701775483",
    "profile_user": "5325971446625758812",
    "balance_coin": "5215420556089776398",
    "diamond_badge": "6068673795793624089",
    "id_badge": "5435907392334215552",
    "deposit_money": "6219646698021463224",
    "sendmoney_shield": "5463424023734014980",
    "bkash_method": "6152327402098793153",
    "nagad_method": "6152331409303280461",
    "rocket_method": "6086803441160558654",
    "binance_method": "5798751138647905130",
    "trx_input": "5814427657609153890",
    "waiting_clock": "6122681660921092237",
    "deposit_success": "6269285159774720688",
    "buy_success": "6269285159774720688",
    "box_package": "5314665894406805639",
    "money_spent": "6219646698021463224",
    "wallet_balance": "5215420556089776398",
    "copy_down": "5435932616677145539",
    "no_stock": "6068743889659892487",
    "insufficient_bal": "6071301770317927702",
    "quantity_icon": "5220149332262528784",
    "choose_select": "5854703064887332338",
    "txt_file_caption": "6109595432441090250",
    "order_pending": "5215484787325676090",
    "order_delivered": "6219954312169136748",
    "loudspeaker": "6219940267626078011",
    "admin_crown": "6188206545277291962",
    "alarm_bell": "6283048296575408684",
    "stats_chart": "5213107179329953547",
    "username_link": "5814427657609153890",
    "telegram_premium_cat": "5789911984283586269",
    "vpn_service_cat": "5998881947328188290",
    "mail_cat": "5354826222331245563",
    "proxy_cat": "5287292843763713628",
    "camera_icon": "5244699979506788336"
}

def pe(key):
    emoji_id = POST_PREMIUM_EMOJIS.get(key, "")
    if emoji_id:
        return f'<tg-emoji emoji-id="{emoji_id}">✨</tg-emoji>'
    return ""

def get_vpn_emoji_key(vpn_name):
    low = vpn_name.lower()
    if "express" in low: return "vpn_express"
    if "cyberghost" in low: return "vpn_cyberghost"
    if "panda" in low: return "vpn_panda"
    if "ipvanish" in low or "ip vanish" in low: return "vpn_ipvanish"
    if "nord" in low: return "vpn_nord"
    if "hma" in low: return "vpn_hma"
    if "pia" in low: return "vpn_pia"
    if "surfshark" in low: return "vpn_surfshark"
    if "bitdefender" in low: return "vpn_bitdefender"
    if "turbo" in low: return "vpn_turbo"
    if "proton" in low: return "vpn_proton"
    return "vpn_service_cat"

PREMIUM_EMOJI_PREFIX = "premium_emoji_"

def save_premium_emoji_mapping(mapping):
    conn = db_connect()
    cursor = conn.cursor()
    for emoji, emoji_id in mapping.items():
        emoji = str(emoji).strip()
        emoji_id = str(emoji_id).strip()
        if emoji and emoji_id.isdigit():
            cursor.execute(
                "INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)",
                (PREMIUM_EMOJI_PREFIX + emoji, emoji_id)
            )
    conn.commit()
    conn.close()

def load_premium_emoji_mapping():
    try:
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT key, value FROM settings WHERE key LIKE ?", (PREMIUM_EMOJI_PREFIX + "%",))
        rows = cursor.fetchall()
        conn.close()
        return {k[len(PREMIUM_EMOJI_PREFIX):]: v for k, v in rows}
    except Exception:
        return {}

def parse_premium_emoji_mapping(file_or_text_content):
    """Parse mappings such as '🔴 = 5788939937335366' from text or a TXT file."""
    mapping = {}
    legacy_entries = {}
    for raw_line in str(file_or_text_content or "").splitlines():
        line = raw_line.strip()
        if not line or line.startswith('#'):
            continue
        parts = [x.strip() for x in re.split(r'\s*\|\s*', line)]
        if len(parts) >= 3 and parts[-1].isdigit():
            emoji = parts[-2]
            if emoji:
                mapping[emoji] = parts[-1]
            if parts[0] and parts[0] != emoji:
                legacy_entries[parts[0]] = parts[-1]
            continue
        match = re.match(r'(.+?)\s*(?:=|:)\s*(\d{10,30})\s*$', line)
        if match:
            emoji, emoji_id = match.group(1).strip(), match.group(2).strip()
            if emoji:
                mapping[emoji] = emoji_id
    return mapping, legacy_entries


def _is_emoji_mapping_key(value):
    """Exclude button-name mappings; only use emoji-only keys in broadcasts."""
    if not value or len(value) > 24:
        return False
    has_emoji = False
    for char in value:
        cp = ord(char)
        is_emoji_codepoint = (
            0x1F000 <= cp <= 0x1FAFF or
            0x2600 <= cp <= 0x27FF or
            0x2300 <= cp <= 0x23FF or
            0x2B00 <= cp <= 0x2BFF or
            0x1F1E6 <= cp <= 0x1F1FF or
            0x1F3FB <= cp <= 0x1F3FF or
            cp in (0x200D, 0xFE0E, 0xFE0F, 0x20E3) or
            0xE0020 <= cp <= 0xE007F
        )
        if not is_emoji_codepoint:
            return False
        if (0x1F000 <= cp <= 0x1FAFF or 0x2600 <= cp <= 0x27FF or
                0x2300 <= cp <= 0x23FF or 0x2B00 <= cp <= 0x2BFF or
                0x1F1E6 <= cp <= 0x1F1FF):
            has_emoji = True
    return has_emoji


def convert_premium_emoji_text(text, mapping=None):
    """Escape plain broadcast text and replace mapped emoji with Telegram custom emoji."""
    if text is None or text == "":
        return text
    raw_text = str(text)
    mapping = mapping if mapping is not None else load_premium_emoji_mapping()
    usable = {
        str(emoji): str(emoji_id)
        for emoji, emoji_id in mapping.items()
        if str(emoji).strip() and str(emoji_id).isdigit() and _is_emoji_mapping_key(str(emoji))
    }
    if not usable:
        return html.escape(raw_text)

    ordered = sorted(usable.keys(), key=len, reverse=True)
    pattern = re.compile("|".join(re.escape(emoji) for emoji in ordered))
    output = []
    last_end = 0
    for match in pattern.finditer(raw_text):
        output.append(html.escape(raw_text[last_end:match.start()]))
        emoji = match.group(0)
        output.append(f'<tg-emoji emoji-id="{usable[emoji]}">{html.escape(emoji)}</tg-emoji>')
        last_end = match.end()
    output.append(html.escape(raw_text[last_end:]))
    return "".join(output)

def _custom_emoji_id_from_text(text):
    if not text:
        return None, text
    mapping = load_premium_emoji_mapping()
    for emoji in sorted(mapping.keys(), key=len, reverse=True):
        if emoji and emoji in text:
            return mapping[emoji], text.replace(emoji, "", 1).strip()
    return None, text

def _emoji_id_for_button(text, emoji_key=None):
    direct_id, clean_text = _custom_emoji_id_from_text(text)
    if direct_id:
        return direct_id, clean_text
    if emoji_key:
        key_value = str(emoji_key).strip()
        if key_value.isdigit():
            return key_value, text
        return PREMIUM_EMOJIS.get(key_value), text
    return None, text

OWNER_PREMIUM_SETTING = "owner_premium"

def update_owner_premium_status(user):
    if not user or user.id != ADMIN_ID: return
    premium = getattr(user, "is_premium", None)
    if premium is None: return
    try:
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (OWNER_PREMIUM_SETTING, "1" if premium else "0"))
        conn.commit()
        conn.close()
    except Exception:
        pass

class _RawCustomEmojiButton:
    def __init__(self, text, emoji_id=None, callback_data=None, url=None):
        self.text = str(text)
        self.emoji_id = str(emoji_id) if emoji_id else None
        self.callback_data = callback_data
        self.url = url

    def to_dict(self):
        data = {"text": self.text}
        if self.emoji_id:
            data["icon_custom_emoji_id"] = self.emoji_id
        if self.callback_data is not None:
            data["callback_data"] = self.callback_data
        if self.url is not None:
            data["url"] = self.url
        return data

    def to_json(self):
        return json.dumps(self.to_dict(), ensure_ascii=False)

def premium_keyboard_button(text, emoji_key=None):
    emoji_id, clean_text = _emoji_id_for_button(text, emoji_key)
    if emoji_id:
        return _RawCustomEmojiButton(clean_text, emoji_id=emoji_id)
    return KeyboardButton(clean_text)

def premium_inline_button(text, emoji_key=None, callback_data=None, url=None):
    emoji_id, clean_text = _emoji_id_for_button(text, emoji_key)
    if emoji_id:
        return _RawCustomEmojiButton(
            clean_text,
            emoji_id=emoji_id,
            callback_data=callback_data,
            url=url,
        )
    if callback_data is not None:
        return InlineKeyboardButton(clean_text, callback_data=callback_data)
    if url is not None:
        return InlineKeyboardButton(clean_text, url=url)
    return InlineKeyboardButton(clean_text)

USER_LOG_FILE = "auto_member_count_user.txt"

def save_user_id_to_file(user_id):
    try:
        existing_ids = set()
        if os.path.exists(USER_LOG_FILE):
            with open(USER_LOG_FILE, "r", encoding="utf-8") as f:
                existing_ids = {line.strip() for line in f if line.strip()}
        if str(user_id) not in existing_ids:
            with open(USER_LOG_FILE, "a", encoding="utf-8") as f:
                f.write(f"{user_id}\n")
    except Exception:
        pass

def check_user_subscription(user_id):
    if ADMIN_ID and user_id == ADMIN_ID: return True
    try:
        member = bot.get_chat_member(FORCE_SUB_CHANNEL, user_id)
        if member.status in ['member', 'administrator', 'creator']: return True
    except Exception:
        pass
    return False

def get_force_sub_markup():
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(
        premium_inline_button("Join Channel", "channel_join", url=f"https://t.me/BotAllUpdateServis"),
        premium_inline_button("Verify", "verify_tick", callback_data="verify_subscription")
    )
    return markup

def get_deposit_amount_markup():
    markup = InlineKeyboardMarkup(row_width=2)
    markup.add(
        premium_inline_button("10 টাকা", "money_10", callback_data="depamt_10"),
        premium_inline_button("20 টাকা", "money_20", callback_data="depamt_20"),
        premium_inline_button("30 টাকা", "money_30", callback_data="depamt_30"),
        premium_inline_button("40 টাকা", "money_40", callback_data="depamt_40")
    )
    return markup

def get_payment_method_markup():
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(
        premium_inline_button("bKash", "bkash", callback_data="paymethod_bKash"),
        premium_inline_button("Nagad", "nagad", callback_data="paymethod_Nagad"),
        premium_inline_button("Rocket", "rocket", callback_data="paymethod_Rocket"),
        premium_inline_button("Binance", "binance", callback_data="paymethod_Binance")
    )
    return markup

def auto_drive_backup_loop():
    if os.environ.get("SQLITE_DRIVE_BACKUP", "0") != "1" or service_account is None:
        return  # PostgreSQL is primary; the old SQLite file is archived/read-only and must not be re-uploaded
    SCOPES = ['https://www.googleapis.com/auth/drive.file']
    SERVICE_ACCOUNT_FILE = 'credentials.json' 
    PARENT_FOLDER_ID = '1Fmf22X9PIWhi1qH5q1pf_4xWGeDOMH6V' 

    while True:
        time.sleep(86400) 
        try:
            if not os.path.exists('shop_bot.db'): continue
            creds = service_account.Credentials.from_service_account_file(SERVICE_ACCOUNT_FILE, scopes=SCOPES)
            service = build('drive', 'v3', credentials=creds)
            query = f"name = 'shop_bot.db' and '{PARENT_FOLDER_ID}' in parents and trashed = false"
            response = service.files().list(q=query, spaces='drive', fields='files(id, name)').execute()
            files = response.get('files', [])
            media = MediaFileUpload('shop_bot.db', resumable=True)
            if files:
                service.files().update(fileId=files[0]['id'], media_body=media).execute()
            else:
                service.files().create(body={'name': 'shop_bot.db', 'parents': [PARENT_FOLDER_ID]}, media_body=media, fields='id').execute()
        except Exception:
            pass

def init_db():
    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute('''CREATE TABLE IF NOT EXISTS users (
                        user_id INTEGER PRIMARY KEY,
                        first_name TEXT,
                        balance REAL DEFAULT 0.0,
                        username TEXT,
                        referred_by INTEGER
                    )''')
    try: cursor.execute("ALTER TABLE users ADD COLUMN first_name TEXT")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE users ADD COLUMN username TEXT")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE users ADD COLUMN referred_by INTEGER")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE users ADD COLUMN referral_deposit_bonus REAL NOT NULL DEFAULT 0.0")
    except pgdb.Error: pass

    cursor.execute('''CREATE TABLE IF NOT EXISTS categories (
                        cat_id TEXT PRIMARY KEY,
                        name TEXT,
                        price REAL,
                        has_emoji INTEGER DEFAULT 1,
                        group_type TEXT DEFAULT 'mail',
                        button_name TEXT,
                        is_active INTEGER NOT NULL DEFAULT 1,
                        created_at TEXT DEFAULT CURRENT_TIMESTAMP
                    )''')
    try: cursor.execute("ALTER TABLE categories ADD COLUMN has_emoji INTEGER DEFAULT 1")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE categories ADD COLUMN group_type TEXT DEFAULT 'mail'")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE categories ADD COLUMN button_name TEXT")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE categories ADD COLUMN is_active INTEGER NOT NULL DEFAULT 1")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE categories ADD COLUMN created_at TEXT")
    except pgdb.Error: pass
    cursor.execute("UPDATE categories SET button_name = name WHERE button_name IS NULL OR button_name = ''")
    cursor.execute("UPDATE categories SET created_at = CURRENT_TIMESTAMP WHERE created_at IS NULL OR created_at = ''")

    cursor.execute('''CREATE TABLE IF NOT EXISTS sub_services (
                        sub_id INTEGER PRIMARY KEY AUTOINCREMENT,
                        cat_id TEXT,
                        sub_name TEXT,
                        price REAL,
                        has_emoji INTEGER DEFAULT 1
                    )''')
    try: cursor.execute("ALTER TABLE sub_services ADD COLUMN has_emoji INTEGER DEFAULT 1")
    except pgdb.Error: pass

    cursor.execute('''CREATE TABLE IF NOT EXISTS stock (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        cat_id TEXT,
                        content TEXT,
                        status TEXT NOT NULL DEFAULT 'available',
                        sold_by INTEGER,
                        sold_at TEXT,
                        order_id TEXT
                    )''')
    try: cursor.execute("ALTER TABLE stock ADD COLUMN status TEXT NOT NULL DEFAULT 'available'")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE stock ADD COLUMN sold_by INTEGER")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE stock ADD COLUMN sold_at TEXT")
    except pgdb.Error: pass
    try: cursor.execute("ALTER TABLE stock ADD COLUMN order_id TEXT")
    except pgdb.Error: pass

    cursor.execute('''CREATE TABLE IF NOT EXISTS stock_sales (
                        sale_id INTEGER PRIMARY KEY AUTOINCREMENT,
                        stock_id INTEGER NOT NULL UNIQUE,
                        cat_id TEXT NOT NULL,
                        category_name TEXT NOT NULL,
                        button_name TEXT,
                        buyer_user_id INTEGER NOT NULL,
                        item_content TEXT NOT NULL,
                        unit_price REAL NOT NULL,
                        order_id TEXT NOT NULL,
                        sold_at TEXT NOT NULL
                    )''')

    cursor.execute('''CREATE TABLE IF NOT EXISTS referral_deposit_bonus_ledger (
                        bonus_id INTEGER PRIMARY KEY AUTOINCREMENT,
                        deposit_request_id TEXT NOT NULL UNIQUE,
                        referrer_id INTEGER NOT NULL,
                        referred_user_id INTEGER NOT NULL,
                        deposit_amount REAL NOT NULL,
                        bonus_amount REAL NOT NULL DEFAULT 0.02,
                        credited_at TEXT NOT NULL
                    )''')

    cursor.execute('''CREATE TABLE IF NOT EXISTS custom_buttons (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        btn_name TEXT,
                        btn_url TEXT
                    )''')
    cursor.execute('''CREATE TABLE IF NOT EXISTS member_sell_orders (
                        order_id TEXT PRIMARY KEY,
                        user_id INTEGER NOT NULL,
                        first_name TEXT,
                        username TEXT,
                        duration_key TEXT NOT NULL,
                        duration_label TEXT NOT NULL,
                        quantity INTEGER NOT NULL,
                        price REAL NOT NULL,
                        target_link TEXT NOT NULL,
                        status TEXT NOT NULL DEFAULT 'pending',
                        created_at TEXT NOT NULL,
                        completed_at TEXT,
                        delivery_text TEXT,
                        refunded_at TEXT
                    )''')
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_member_sell_orders_user ON member_sell_orders(user_id, created_at)")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_member_sell_orders_status ON member_sell_orders(status, created_at)")
    cursor.execute('''CREATE TABLE IF NOT EXISTS settings (
                        key TEXT PRIMARY KEY,
                        value TEXT
                    )''')

    cursor.execute("CREATE INDEX IF NOT EXISTS idx_stock_category_status_id ON stock(cat_id, status, id)")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_stock_sales_category ON stock_sales(cat_id, sold_at)")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_referral_bonus_referrer ON referral_deposit_bonus_ledger(referrer_id, credited_at)")

    # These views make each service/button and its live inventory totals easy to inspect in SQLite viewers.
    cursor.execute("DROP VIEW IF EXISTS category_stock_summary")
    cursor.execute('''CREATE VIEW category_stock_summary AS
        SELECT
            c.cat_id AS category_id,
            c.name AS category_name,
            COALESCE(NULLIF(c.button_name, ''), c.name) AS button_name,
            c.group_type AS group_type,
            c.price AS unit_price,
            c.is_active AS is_active,
            COUNT(s.id) AS total_stock,
            SUM(CASE WHEN s.status = 'available' THEN 1 ELSE 0 END) AS available_stock,
            SUM(CASE WHEN s.status = 'sold' THEN 1 ELSE 0 END) AS sold_stock,
            SUM(CASE WHEN s.status = 'removed' THEN 1 ELSE 0 END) AS removed_stock
        FROM categories c
        LEFT JOIN stock s ON s.cat_id = c.cat_id
        GROUP BY c.cat_id, c.name, c.button_name, c.group_type, c.price, c.is_active''')

    cursor.execute("DROP VIEW IF EXISTS stock_details")
    cursor.execute('''CREATE VIEW stock_details AS
        SELECT
            s.id AS stock_id,
            s.cat_id AS category_id,
            COALESCE(c.name, s.cat_id) AS category_name,
            COALESCE(NULLIF(c.button_name, ''), c.name, s.cat_id) AS button_name,
            s.content AS stock_content,
            s.status AS stock_status,
            s.sold_by AS sold_by_user_id,
            s.sold_at AS sold_at,
            s.order_id AS order_id,
            ss.unit_price AS sold_unit_price,
            ss.buyer_user_id AS buyer_user_id
        FROM stock s
        LEFT JOIN categories c ON c.cat_id = s.cat_id
        LEFT JOIN stock_sales ss ON ss.stock_id = s.id''')

    conn.commit()

    default_settings = {
        'bkash_num': '+8801842145918',
        'nagad_num': '+8801842145918',
        'rocket_num': '+8801842145918',
        'binance_uid': '1123474021',
        'get_code_link': 'https://dongvanfb.net/read_mail_box/',
        'pc_directory_path': '',
        'pc_live_money_path': '',
        'pc_live_stock_path': ''
    }
    for k, v in default_settings.items():
        cursor.execute("INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)", (k, v))
    conn.commit()

    default_posts = {
        'welcome_msg': (
            f"{pe('welcome_heart')} <b>Welcome {{first_name}}!</b> {pe('welcome_shop')} আমাদের Shop এ আপনাকে স্বাগতম።\n\n"
            f"{pe('list_point')} এখানে কম মূল্যে পেয়ে যাবেন:\n\n"
            f"{pe('list_point')} Premium Proxy\n"
            f"{pe('list_point')} Premium VPN\n"
            f"{pe('list_point')} Hotmail Account (High quality)\n"
            f"{pe('list_point')} Outlook Account (High quality)\n"
            f"{pe('list_point')} Telegram Premium Buy\n\n"
            f"{pe('trusted_badge')} <b>Trusted service</b>\n"
            f"{pe('fast_speed')} <b>Auto fast service</b>\n\n"
            f"{pe('down_arrow')} নিচের মেনু বাটনগুলো ব্যবহার করুন:"
        ),
        'not_joined_msg': (
            f"{pe('warn_icon')} <b>আপনি আমাদের চ্যানেলে Join করেননি!</b>\n\n"
            f"{pe('step_tick')} বট ব্যবহার করতে প্রথমে Join Channel এ ক্লিক করে জয়েন করুন, এরপর Verify বাটনে ক্লিক করুন।"
        ),
        'support_msg': f"{pe('support_headphone')} <b>যেকোনো প্রয়োজনে আমাদের সাপোর্ট আইডিতে যোগাযোগ করুন:</b>\nhttps://t.me/FBbuysellAX",
        'deposit_info_msg': (
            f"{pe('deposit_money')} <b>আপনি কত টাকা ডিপোজিট করতে চান সংখ্যাটি লিখে পাঠান:</b>\n\n"
            f"{pe('list_point')} সর্বনিম্ন ১০ টাকা {pe('deposit_money')}\n"
            f"{pe('list_point')} সর্বোচ্চ ১০০০০ টাকা {pe('deposit_money')}"
        )
    }

    for key, val in default_posts.items():
        cursor.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (key, val))
    conn.commit()

    # Screenshot-matched Mail and Proxy buttons. Existing IDs are reused where possible
    # so any stock already attached to those IDs remains linked to the same service.
    screenshot_categories = [
        ("hotmail", "Hotmail Trusted", 0.8, "mail"),
        ("outlook", "Outlook Trusted", 0.8, "mail"),
        ("Outlook fr", "Outlook Fr.", 0.85, "mail"),
        ("proxy_9_100", "9 proxy (100MB)", 15.0, "proxy"),
        ("proxy", "9 proxy (200MB)", 27.0, "proxy"),
        ("proxy_711_100", "711 Proxy (100 MB)", 12.0, "proxy"),
        ("proxy_711_200", "711 Proxy (200 MB)", 22.0, "proxy"),
        ("proxy_h143_100", "H143 Proxy (100MB)", 7.0, "proxy"),
        ("proxy_h143_200", "H143 Proxy (200MB)", 15.0, "proxy"),
        ("proxy_rapid_100", "Rapid Proxy (100MB)", 13.0, "proxy"),
        ("proxy_rapid_200", "Rapid Proxy (200MB)", 24.0, "proxy"),
        ("proxy_loki_100", "Loki Proxy (100MB)", 12.0, "proxy"),
    ]
    cursor.execute("SELECT value FROM settings WHERE key = 'screenshot_proxy_mail_seed_v1'")
    screenshot_seed_done = cursor.fetchone() is not None
    for default_cat_id, default_name, default_price, default_group in screenshot_categories:
        if screenshot_seed_done:
            # Add missing default buttons, but never overwrite later Admin edits on restart.
            cursor.execute(
                "INSERT OR IGNORE INTO categories (cat_id, name, price, has_emoji, group_type, button_name, is_active, created_at) "
                "VALUES (?, ?, ?, 1, ?, ?, 1, CURRENT_TIMESTAMP)",
                (default_cat_id, default_name, default_price, default_group, default_name),
            )
        else:
            # One-time migration from the old built-in labels/prices; preserve linked stock rows.
            cursor.execute(
                "INSERT INTO categories (cat_id, name, price, has_emoji, group_type, button_name, is_active, created_at) "
                "VALUES (?, ?, ?, 1, ?, ?, 1, CURRENT_TIMESTAMP) "
                "ON CONFLICT(cat_id) DO UPDATE SET name=excluded.name, price=excluded.price, has_emoji=1, "
                "group_type=excluded.group_type, button_name=excluded.button_name, is_active=1",
                (default_cat_id, default_name, default_price, default_group, default_name),
            )

    if not screenshot_seed_done:
        # This was an old built-in Mail entry, not part of the supplied screenshot list.
        # Keep its row/stock intact but hide it from the customer Mail menu.
        cursor.execute("UPDATE categories SET is_active = 0 WHERE cat_id = 'Ig Hotmail'")
        cursor.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('screenshot_proxy_mail_seed_v1', '1')")

    cursor.execute("SELECT COUNT(*) FROM sub_services WHERE cat_id = 'telegram_premium'")
    if cursor.fetchone()[0] == 0:
        cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('telegram_premium', 'Telegram Premium (3 Month)', 2010.0, 1)")
        cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('telegram_premium', 'Telegram Premium (6 Month)', 2520.0, 1)")
        cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('telegram_premium', 'Telegram Premium (12 Month)', 4030.0, 1)")

    cursor.execute("DELETE FROM sub_services WHERE cat_id IN ('vpn_3d', 'vpn_7d', 'vpn_14d', 'vpn_30d')")
    
    vpn_3d_list = ["Express VPN", "Cyberghost VPN", "Panda VPN", "IP Vanish VPN"]
    for v in vpn_3d_list:
        sub_n = f"{v} (3 Day)"
        cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('vpn_3d', ?, 20.0, 1)", (sub_n,))

    vpn_7d_list = ["Nord VPN", "HMA VPN", "PIA VPN", "Surfshark VPN", "Bitdefender VPN", "Turbo VPN"]
    for v in vpn_7d_list:
        sub_n = f"{v} (7 Day)"
        cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('vpn_7d', ?, 30.0, 1)", (sub_n,))

    vpn_14d_list = ["Proton VPN"]
    for v in vpn_14d_list:
        sub_n = f"{v} (14 Day)"
        cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('vpn_14d', ?, 50.0, 1)", (sub_n,))

    cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('vpn_30d', 'Nord VPN (30 Day)', 210.0, 1)")
    cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('vpn_30d', 'Hma VPN (30 Day)', 110.0, 1)")
    cursor.execute("INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES ('vpn_30d', 'Proton VPN (30 Day)', 160.0, 1)")

    conn.commit()
    conn.close()

_applied_migrations = pgdb.apply_migrations()   # versioned, idempotent, non-destructive


def _refuse_start_if_old_data_not_migrated():
    """Safety: the old bot left your data in PostgreSQL as ONE blob (bot_sqlite_backup). If that blob exists but the
    real tables are still empty, starting now would show every user a 0 balance. Stop and tell the admin instead."""
    c = db_connect()
    try:
        has_blob = c.execute("SELECT to_regclass('bot_sqlite_backup')").fetchone()[0]
        if not has_blob:
            return
        blob = c.execute("SELECT length(db_data) FROM bot_sqlite_backup WHERE id = 1").fetchone()
        n_users = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
    finally:
        c.close()
    if blob and blob[0] and n_users == 0 and os.environ.get("ALLOW_EMPTY_START", "0") != "1":
        raise SystemExit(
            "STOP: your old data is still inside PostgreSQL as the legacy backup blob (bot_sqlite_backup) and the new tables are empty.\n"
            "Run the one-time migration first:  python migrate_once.py   (dry-run), then  python migrate_once.py --apply --backup-file <pg_dump file>\n"
            "(set ALLOW_EMPTY_START=1 only if you really want a brand-new empty shop)")


_refuse_start_if_old_data_not_migrated()
init_db()

# ----------------- SMS Gateway / Binance payment integration -----------------
pgw.configure()
pgw.init_schema()
pgw.bootstrap_device_from_env()
app.register_blueprint(pgw.gateway_bp)


def _gw_admin_chat():
    target = ADMIN_ID
    group = get_setting_msg('deposit_group_id', '')
    if group:
        try:
            target = int(group)
        except ValueError:
            target = group
    return target


def _gw_notify_user(uid, text):
    try:
        bot.send_message(uid, text, reply_markup=get_permanent_keyboard(uid))
    except Exception as e:
        print(f"[gateway] could not notify user {uid}: {e}")


def _gw_notify_admin(text, deposit_id=None):
    markup = None
    if deposit_id:
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("✅ Approve", callback_data=f"gwapp_{deposit_id}"),
                   InlineKeyboardButton("❌ Reject", callback_data=f"gwrej_{deposit_id}"))
    try:
        bot.send_message(_gw_admin_chat(), text, reply_markup=markup)
    except Exception as e:
        print(f"[gateway] could not notify admin: {e}")


pgw.configure(notify_user=_gw_notify_user, notify_admin=_gw_notify_admin)


def _gw_start_binance_order(call, user_id, amt):
    """Official Binance Pay Merchant API order."""
    u = call.from_user
    uname = f"@{u.username}" if u.username else "N/A"
    try:
        o = pgw.create_merchant_order(user_id, uname, u.first_name or "N/A", amt)
    except Exception as e:
        print(f"[binance] order creation failed: {e}")
        bot.send_message(call.message.chat.id, "⚠️ Binance Pay অর্ডার তৈরি করা যায়নি। কিছুক্ষণ পরে আবার চেষ্টা করুন।")
        return
    user_temp_deposit.pop(user_id, None)
    kb = InlineKeyboardMarkup()
    link = o.get("checkoutUrl") or o.get("universalUrl")
    if link:
        kb.add(InlineKeyboardButton("💳 Binance Pay দিয়ে পেমেন্ট করুন", url=link))
    bot.send_message(
        call.message.chat.id,
        f"আপনি <b>Binance Pay</b> সিলেক্ট করেছেন।\n\nপরিমাণ: <b>{o['usd']} USDT</b> (৳{int(amt)})\n"
        f"অর্ডার ১৫ মিনিট পর্যন্ত বৈধ। পেমেন্ট সম্পন্ন হলে স্বয়ংক্রিয়ভাবে ব্যালেন্স যোগ হবে — স্ক্রিনশট বা TxID লাগবে না।",
        parse_mode="HTML", reply_markup=kb)


def _gw_submit_trx(message, user_id, text):
    d = user_temp_deposit[user_id]
    method = d.get("method", "")
    provider = method.lower()
    u = message.from_user
    uname = f"@{u.username}" if u.username else "N/A"
    expected_foreign = None
    if provider == "binance":
        expected_foreign = pgw.to_minor((pgw.Decimal(str(d["amount"])) / pgw.BDT_PER_USD))
    try:
        dep = pgw.create_deposit(user_id, uname, u.first_name or "N/A", provider, d["amount"], text.strip(),
                                 expected_foreign_minor=expected_foreign)
    except ValueError as e:
        bot.send_message(user_id, f"⚠️ {e}। সঠিক ট্রানজেকশন আইডি লিখে আবার পাঠান।", reply_markup=get_permanent_keyboard(user_id))
        return
    del user_temp_deposit[user_id]
    if dep["status"] == "APPROVED":
        return  # the gateway already credited the user and sent the success message
    bot.send_message(
        user_id,
        f"{pe('waiting_clock')} <b>আপনার ট্রানজেকশন আইডি গ্রহণ করা হয়েছে।</b>\nপেমেন্ট যাচাই হচ্ছে — নিশ্চিত হলেই স্বয়ংক্রিয়ভাবে ব্যালেন্স যোগ হবে, স্ক্রিনশট লাগবে না।",
        parse_mode="HTML", reply_markup=get_permanent_keyboard(user_id))
    if provider == "binance":
        threading.Thread(target=lambda: _safe(pgw.reconcile_binance_history), daemon=True).start()


def _safe(fn):
    try:
        fn()
    except Exception as e:
        print(f"[gateway] background check failed: {e}")


def _gw_status_text():
    st = pgw.admin_stats()
    rc = pgw.reconciler_status()
    return (
        "<b>SMS Gateway & Payments</b>\n\n"
        f"SMS devices registered: <b>{st['devices']}</b> (last seen: {st['last_device_seen'] or 'never'})\n"
        f"Reconciler last run: {rc['last_run'] or 'not yet'}{' | last error: ' + html.escape(rc['last_error']) if rc['last_error'] else ''}\n"
        f"Binance Pay merchant API: <b>{'configured' if pgw.merchant_configured() else 'not configured'}</b>\n"
        f"Binance UID/history check: <b>{'configured' if pgw.binance_history_configured() else 'not configured'}</b>\n\n"
        f"Verified deposits: <b>{st['verified']}</b>\nPending: <b>{st['pending']}</b>\nFailed/rejected: <b>{st['failed']}</b>\n"
        f"Unmatched SMS payments: <b>{st['unmatched']}</b>\nNeeds review: <b>{st['review']}</b>\nDuplicate alerts: <b>{st['dupes']}</b>")


def _gw_deposit_line(d):
    return (f"#{d['id']} • {d['provider']} • ৳{pgw.minor_str(d['amount_minor'])} • user {d['user_id']} {d['username'] or ''} • "
            f"<code>{html.escape(d['provider_trx_id'])}</code> • <b>{d['status']}</b>" + (f" • {html.escape(d['review_reason'])}" if d['review_reason'] else ""))


def _handle_gateway_callback(call, user_id):
    data = call.data
    if not (data.startswith("gwapp_") or data.startswith("gwrej_") or data.startswith("admin_gw_")):
        return False
    if user_id != ADMIN_ID:
        bot.answer_callback_query(call.id, "Admin only", show_alert=True)
        return True
    chat = call.message.chat.id
    if data.startswith("gwapp_") or data.startswith("gwrej_"):
        dep_id = int(data.split("_")[1])
        if data.startswith("gwapp_"):
            res = pgw.admin_approve(dep_id, user_id)
            bot.answer_callback_query(call.id, "Approved" if res else "Already processed", show_alert=not res)
        else:
            dep = pgw.admin_reject(dep_id, user_id)
            if dep:
                try:
                    bot.send_message(dep["user_id"], f"{pe('warn_icon')} আপনার ডিপোজিট যাচাই করা যায়নি, তাই রিজেক্ট করা হয়েছে। সঠিক তথ্য দিয়ে আবার চেষ্টা করুন।", parse_mode="HTML")
                except Exception:
                    pass
            bot.answer_callback_query(call.id, "Rejected" if dep else "Already processed", show_alert=not dep)
        try:
            bot.edit_message_reply_markup(chat, call.message.message_id, reply_markup=None)
        except Exception:
            pass
        return True
    if data == "admin_gw_menu":
        mk = InlineKeyboardMarkup(row_width=1)
        mk.add(InlineKeyboardButton("📊 Gateway status", callback_data="admin_gw_status"),
               InlineKeyboardButton("⏳ Pending / review deposits", callback_data="admin_gw_pending"),
               InlineKeyboardButton("🔎 Search user ID / TrxID", callback_data="admin_gw_search"),
               InlineKeyboardButton("🔑 New SMS device token", callback_data="admin_gw_newdevice"),
               InlineKeyboardButton("🟡 Test Binance API key", callback_data="admin_gw_binance_test"),
               InlineKeyboardButton("⬅️ Back to Admin", callback_data="admin_main"))
        bot.send_message(chat, _gw_status_text(), parse_mode="HTML", reply_markup=mk)
    elif data == "admin_gw_status":
        bot.send_message(chat, _gw_status_text(), parse_mode="HTML")
    elif data == "admin_gw_pending":
        c = pgw._conn()
        try:
            rows = c.execute("SELECT * FROM pending_deposits WHERE status IN ('PENDING','PENDING_REVIEW') ORDER BY id DESC LIMIT 15").fetchall()
        finally:
            c.close()
        if not rows:
            bot.send_message(chat, "No pending deposits.")
        for r in rows:
            mk = InlineKeyboardMarkup()
            mk.add(InlineKeyboardButton("✅ Approve", callback_data=f"gwapp_{r['id']}"), InlineKeyboardButton("❌ Reject", callback_data=f"gwrej_{r['id']}"))
            bot.send_message(chat, _gw_deposit_line(r), parse_mode="HTML", reply_markup=mk)
    elif data == "admin_gw_binance_test":
        bot.answer_callback_query(call.id, "Checking...")
        ok, msg = pgw.binance_selftest()
        hint = "" if ok else "\n\nCommon causes: wrong key/secret, 'Enable Reading' not ticked, IP restriction does not include this VPS IP, system clock off."
        bot.send_message(chat, ("✅ " if ok else "❌ ") + html.escape(msg) + hint, parse_mode="HTML")
        return True
    elif data == "admin_gw_search":
        admin_states[user_id] = {"action": "gw_search"}
        bot.send_message(chat, "Telegram user ID অথবা Transaction ID লিখে পাঠান:")
    elif data == "admin_gw_newdevice":
        admin_states[user_id] = {"action": "gw_newdevice"}
        bot.send_message(chat, "Merchant ID লিখে পাঠান (যেমন <code>MERCHANT001</code>). এই ID-ই SMS Reader X অ্যাপে বসাতে হবে। টোকেন শুধু একবার দেখানো হবে।", parse_mode="HTML")
    bot.answer_callback_query(call.id)
    return True


def _gw_admin_text(message, user_id, text):
    """Admin text input for the gateway menu. Returns True when handled."""
    action = admin_states.get(user_id, {}).get("action")
    if action == "gw_search":
        del admin_states[user_id]
        deps, txs = pgw.search_payments(text)
        if not deps and not txs:
            bot.reply_to(message, "Nothing found.")
            return True
        out = [_gw_deposit_line(d) for d in deps] + [
            f"SMS payment: {t['provider']} ৳{pgw.minor_str(t['amount_minor'])} <code>{html.escape(t['provider_trx_id'])}</code> <b>{t['status']}</b> {html.escape(t['status_reason'] or '')}" for t in txs]
        bot.reply_to(message, "\n".join(out)[:3900], parse_mode="HTML")
        if deps:
            hist = pgw.audit_history(deps[0]["public_id"])
            if hist:
                bot.send_message(message.chat.id, "<b>Audit</b>\n" + "\n".join(f"{h['ts']} {h['action']} {html.escape(h['details'] or '')}" for h in hist)[:3800], parse_mode="HTML")
        return True
    if action == "gw_newdevice":
        del admin_states[user_id]
        merchant = re.sub(r"[^A-Za-z0-9_-]", "", text)[:40]
        if not merchant:
            bot.reply_to(message, "Invalid Merchant ID.")
            return True
        token = pgw.create_device(merchant, "android")
        bot.reply_to(message, f"Merchant ID: <code>{merchant}</code>\nBearer token (save it now, it is not stored):\n<code>{token}</code>", parse_mode="HTML")
        return True
    return False

def get_setting_msg(key, default=""):
    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("SELECT value FROM settings WHERE key = ?", (key,))
    res = cursor.fetchone()
    conn.close()
    return res[0] if res else default


# Exact button emoji IDs from the supplied Proxy/Mail screenshots.
CATEGORY_EMOJI_SETTING_PREFIX = "category_emoji_id:"
CATEGORY_EMOJI_IDS = {
    "hotmail": "5354826222331245563",
    "outlook": "5354826222331245563",
    "Outlook fr": "5354826222331245563",
    "proxy": "6143321667427904097",  # Existing proxy row is reused for 9 Proxy (200MB).
    "proxy_9_100": "6143321667427904097",
    "proxy_711_100": "6143393822878475954",
    "proxy_711_200": "6143393822878475954",
    "proxy_h143_100": "5375177250553487549",
    "proxy_h143_200": "5375177250553487549",
    "proxy_rapid_100": "6143192522056283070",
    "proxy_rapid_200": "6143192522056283070",
    "proxy_loki_100": "6147909495658913509",
}


def get_category_button_emoji_key(cat_id, name, group_type, has_emoji=1):
    """Return saved custom emoji ID or the screenshot-matched service emoji."""
    if not has_emoji:
        return None
    custom_id = get_setting_msg(CATEGORY_EMOJI_SETTING_PREFIX + str(cat_id), "")
    if str(custom_id).isdigit():
        return str(custom_id)
    low = (name or "").lower()
    if group_type == "mail":
        return PREMIUM_EMOJIS["mail_service_item"]
    if "711" in low:
        return PREMIUM_EMOJIS["proxy_711_item"]
    if "h143" in low or "h14" in low:
        return PREMIUM_EMOJIS["proxy_h143_item"]
    if "rapid" in low:
        return PREMIUM_EMOJIS["proxy_rapid_item"]
    if "loki" in low:
        return PREMIUM_EMOJIS["proxy_loki_item"]
    if "9 proxy" in low or "9proxy" in low:
        return PREMIUM_EMOJIS["proxy_9_item"]
    if cat_id in CATEGORY_EMOJI_IDS:
        return CATEGORY_EMOJI_IDS[cat_id]
    return PREMIUM_EMOJIS["proxy_item"]


def get_sub_service_button_emoji_key(sub_id, has_emoji=1, fallback=None):
    if not has_emoji:
        return None
    custom_id = get_setting_msg("sub_service_emoji_id:" + str(sub_id), "")
    return str(custom_id) if str(custom_id).isdigit() else fallback


def _save_pending_button(pending_data, has_emoji, custom_emoji_id=None):
    """Create/update a category or sub-service using the same Add/Edit save path."""
    mode = pending_data.get("mode")
    conn = db_connect()
    cur = conn.cursor()
    saved_id = None
    name = pending_data.get("name", "")
    price = float(pending_data.get("price", 0))

    if mode == "new_cat":
        clean_id_base = "".join(c for c in name.lower() if c.isalnum() or c == "_")[:12] or "service"
        saved_id = f"{clean_id_base}_{str(uuid.uuid4())[:6]}"
        group_type = "proxy" if "proxy" in name.lower() else "mail"
        cur.execute(
            "INSERT INTO categories (cat_id, name, price, has_emoji, group_type, button_name, is_active, created_at) VALUES (?, ?, ?, ?, ?, ?, 1, CURRENT_TIMESTAMP)",
            (saved_id, name, price, int(bool(has_emoji)), group_type, name),
        )
        emoji_setting_key = CATEGORY_EMOJI_SETTING_PREFIX + saved_id
    elif mode == "edit_cat":
        saved_id = str(pending_data["cat_id"])
        cur.execute(
            "UPDATE categories SET name = ?, button_name = ?, price = ?, has_emoji = ? WHERE cat_id = ?",
            (name, name, price, int(bool(has_emoji)), saved_id),
        )
        emoji_setting_key = CATEGORY_EMOJI_SETTING_PREFIX + saved_id
    elif mode == "new_sub":
        cur.execute(
            "INSERT INTO sub_services (cat_id, sub_name, price, has_emoji) VALUES (?, ?, ?, ?)",
            (pending_data["cat_id"], name, price, int(bool(has_emoji))),
        )
        saved_id = str(cur.lastrowid)
        emoji_setting_key = "sub_service_emoji_id:" + saved_id
    elif mode == "edit_sub":
        saved_id = str(pending_data["sub_id"])
        cur.execute(
            "UPDATE sub_services SET sub_name = ?, price = ?, has_emoji = ? WHERE sub_id = ?",
            (name, price, int(bool(has_emoji)), saved_id),
        )
        emoji_setting_key = "sub_service_emoji_id:" + saved_id
    else:
        conn.close()
        raise ValueError(f"Unsupported button edit mode: {mode}")

    if custom_emoji_id:
        cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (emoji_setting_key, str(custom_emoji_id)))
    elif not has_emoji:
        cur.execute("DELETE FROM settings WHERE key = ?", (emoji_setting_key,))

    conn.commit()
    conn.close()
    return saved_id

def get_permanent_keyboard(user_id):
    markup = ReplyKeyboardMarkup(resize_keyboard=True)
    markup.row(
        premium_keyboard_button("All Services", "all_services"),
        premium_keyboard_button("Deposit", "deposit")
    )
    markup.row(
        premium_keyboard_button("Profile", "profile"),
        premium_keyboard_button("Support", "support")
    )
    markup.row(
        premium_keyboard_button("Get Code", "get_code"),
        premium_keyboard_button("Referral", "referral")
    )
    if user_id == ADMIN_ID:
        markup.row(
            premium_keyboard_button("Admin Panel", "admin_panel"),
            premium_keyboard_button("Search User ID", "search_user")
        )
    markup.row(premium_keyboard_button("Restart Bot", "restart"))
    return markup

def main_menu_inline(user_id):
    markup = InlineKeyboardMarkup(row_width=2)
    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("SELECT btn_name, btn_url FROM custom_buttons")
    custom_btns = cursor.fetchall()
    conn.close()
    for b_name, b_url in custom_btns:
        markup.add(premium_inline_button(b_name, "home_button", url=b_url))
    return markup

def get_categories_markup():
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(
        premium_inline_button("Mail Service", "mail_cat", callback_data="group_mail"),
        premium_inline_button("Proxy Service", "proxy_cat", callback_data="group_proxy"),
        premium_inline_button("Telegram Premium Buy", "telegram_premium_cat", callback_data="special_cat_telegram_premium"),
        premium_inline_button("VPN Service", "vpn_service_cat", callback_data="special_cat_vpn_service"),
        premium_inline_button("Telegram Member Sell", "5884079687709234720", callback_data="member_sell")
    )
    return markup


# ----------------- Telegram Member Sell (isolated new service) -----------------
# Custom emoji IDs supplied by the owner for each Telegram Member Sell message field.
MEMBER_SELL_TEXT_EMOJI = "5884079687709234720"
MEMBER_SELL_EMOJIS = {
    "service": "5884079687709234720",
    "duration": "5296370519136812159",
    "delivery": "6267229004311303657",
    "fast": "5415681936070821017",
    "down": "6071406125138318025",
    "menu_description": "4943195336911881191",
    "prompt_members": "6244387315964188652",
    "prompt_price": "6296202896639791835",
    "prompt_target": "6275878213746955453",
    "success_order_id": "6131684255970891449",
    "success_balance": "5287231198098117669",
    "delivery_info": "6188206545277291962",
    "thanks": "6292078018638651747",
    "admin_name": "5256143829672672750",
    "admin_username": "6307589808424228455",
    "admin_user_id": "6307777408300753473",
    "admin_link": "6068777875736109056",
    "admin_status": "6068697658631919093",
    "refund_notice": "5854796227022949904",
    "refund_amount": "5391090636961099009",
}
MEMBER_SELL_PLANS = {
    "30": {
        "label": "30 Day",
        "heading": "30 Day Service",
        "delivery": "Only 10 minutes",
        "packages": [(100, 35), (200, 60), (500, 100), (1000, 150), (2000, 300)],
    },
    "90": {
        "label": "3 Month",
        "heading": "3 Month Service",
        "delivery": "Only 20 minutes",
        "packages": [(500, 130), (1000, 250), (2000, 500)],
    },
    "365": {
        "label": "1 Year",
        "heading": "1 Years Service",
        "delivery": "Only 30 minutes",
        "packages": [(500, 210), (1000, 400), (2000, 800)],
    },
}


def member_sell_emoji(emoji_id, fallback="✨"):
    return f'<tg-emoji emoji-id="{emoji_id}">{fallback}</tg-emoji>'


def is_valid_member_sell_target(value):
    """Accept Telegram public usernames and t.me/telegram.me public or invite links."""
    value = (value or "").strip()
    if re.fullmatch(r"@?[A-Za-z0-9_]{5,32}", value):
        return True
    return bool(re.fullmatch(
        r"(?i)(?:https?://)?(?:www\.)?(?:t\.me|telegram\.me)/[A-Za-z0-9_+/-]+(?:\?[A-Za-z0-9_=&%+.-]*)?/?",
        value
    ))


def get_member_sell_order(order_id):
    conn = db_connect()
    cur = conn.cursor()
    cur.execute(
        "SELECT order_id, user_id, first_name, username, duration_label, quantity, price, target_link, status "
        "FROM member_sell_orders WHERE order_id = ?",
        (order_id,)
    )
    row = cur.fetchone()
    conn.close()
    return row

def get_admin_markup():
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(
        premium_inline_button("Bot Analytics & Users", "analytics", callback_data="admin_analytics"),
        premium_inline_button("Auto Count Member ID", "member_count_file", callback_data="admin_auto_member_count"),
        premium_inline_button("All Member Balance List", "balance_list", callback_data="admin_member_balance_list"),
        premium_inline_button("Download Balance List TXT", "download_txt", callback_data="admin_download_balance_txt"),
        premium_inline_button("Recover Balance List (.txt)", "recover_balance", callback_data="admin_recover_balance_list"),
        premium_inline_button("Broadcast Message", "live_broadcast", callback_data="admin_broadcast"),
        premium_inline_button("Live Analysis & User Broadcast Message", "live_broadcast", callback_data="admin_live_broadcast"),
        premium_inline_button("Premium Emoji Set", "button_edit", callback_data="admin_premium_emoji_set"),
        premium_inline_button("Payment Method Edit", "edit_service", callback_data="admin_payment_method_edit"),
        premium_inline_button("All Details Download Directory PC", "download_txt", callback_data="admin_pc_directory_setup"),
        premium_inline_button("All Live Analysis & Money Directive PC Download", "download_txt", callback_data="admin_pc_live_money_setup"),
        premium_inline_button("Only Stock Available Directive PC Download", "download_txt", callback_data="admin_pc_live_stock_setup"),
        premium_inline_button("Add Member Money Back", "add_balance", callback_data="admin_add_member_balance"),
        premium_inline_button("Remove Money", "remove_money", callback_data="admin_remove_member_balance"),
        premium_inline_button("Update Back All Money Member", "bulk_update", callback_data="admin_bulk_money_update"),
        premium_inline_button("All Post Edit", "post_edit", callback_data="admin_all_post_edit"),
        premium_inline_button("All Button Edit", "button_edit", callback_data="admin_all_button_edit"),
        premium_inline_button("Edit Prices & Services", "edit_service", callback_data="admin_edit_services"),
        premium_inline_button("Manage Stock (Add/Remove)", "manage_stock", callback_data="admin_add_stock_menu"),
        InlineKeyboardButton("SMS Gateway & Payments", callback_data="admin_gw_menu")
    )
    return markup

def pc_directory_export_loop():
    while True:
        time.sleep(15)
        try:
            timestamp_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            date_only = datetime.now().strftime("%Y-%m-%d")
            
            path1 = get_setting_msg("pc_directory_path", "")
            if path1 and os.path.exists(path1):
                conn = db_connect()
                cur = conn.cursor()
                cur.execute("SELECT user_id, first_name, balance, username FROM users")
                all_u = cur.fetchall()
                
                with open(os.path.join(path1, f"bot_analysis_user_{date_only}.txt"), "w", encoding="utf-8") as f:
                    f.write(f"--- Last Updated: {timestamp_str} ---\n")
                    for uid, fn, bal, un in all_u:
                        f.write(f"ID: {uid} | Name: {fn} | Username: {un} | Balance: {bal}\n")
                
                with open(os.path.join(path1, f"auto_member_count_user_{date_only}.txt"), "w", encoding="utf-8") as f:
                    f.write(f"--- Last Updated: {timestamp_str} ---\n")
                    for uid, _, _, _ in all_u:
                        f.write(f"{uid}\n")

                cur.execute("SELECT user_id, balance FROM users WHERE balance > 0")
                with open(os.path.join(path1, f"all_member_balance_list_{date_only}.txt"), "w", encoding="utf-8") as f:
                    f.write(f"--- Last Updated: {timestamp_str} ---\n")
                    for uid, bal in cur.fetchall():
                        f.write(f"{uid} | {bal}\n")
                conn.close()

            path2 = get_setting_msg("pc_live_money_path", "")
            if path2 and os.path.exists(path2):
                conn = db_connect()
                cur = conn.cursor()
                cur.execute("SELECT user_id, first_name, balance, username FROM users")
                all_u = cur.fetchall()
                with open(os.path.join(path2, "all_time_balance_and_uid_analysis.txt"), "w", encoding="utf-8") as f:
                    f.write(f"--- Live Bot Money Analysis [Updated: {timestamp_str}] ---\n")
                    for uid, fn, bal, un in all_u:
                        f.write(f"UID: {uid} | Name: {fn} | Username: {un} | Balance: ৳{bal}\n")
                conn.close()

            path3 = get_setting_msg("pc_live_stock_path", "")
            if path3 and os.path.exists(path3):
                conn = db_connect()
                cur = conn.cursor()
                cur.execute("SELECT cat_id, content FROM stock WHERE status = 'available'")
                stocks = cur.fetchall()
                with open(os.path.join(path3, "live_available_stock_details.txt"), "w", encoding="utf-8") as f:
                    f.write(f"--- Live Stock Available [Updated: {timestamp_str}] ---\n")
                    for cid, cnt in stocks:
                        f.write(f"Category: {cid} -> {cnt}\n")
                conn.close()

        except Exception as e:
            print(f"PC directory export error: {e}")

t_pc_export = threading.Thread(target=pc_directory_export_loop, daemon=True)
t_pc_export.start()

@bot.message_handler(func=lambda message: message.text and "Restart Bot" in message.text)
@bot.message_handler(commands=['start'])
def send_welcome(message):
    update_owner_premium_status(message.from_user)
    user_id = message.from_user.id
    first_name = message.from_user.first_name or "User"
    username = f"@{message.from_user.username}" if message.from_user.username else "N/A"
    
    save_user_id_to_file(user_id)

    args = message.text.split()
    referred_by = None
    if len(args) > 1:
        try:
            ref_id = int(args[1])
            if ref_id != user_id:
                referred_by = ref_id
        except ValueError:
            pass

    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("SELECT user_id, referred_by FROM users WHERE user_id = ?", (user_id,))
    existing_user = cursor.fetchone()
    
    if not existing_user:
        cursor.execute("INSERT INTO users (user_id, first_name, balance, username, referred_by) VALUES (?, ?, 0.0, ?, ?)", (user_id, first_name, username, referred_by))
        conn.commit()
        
        if referred_by:
            # আপডেট লজিক: রেফারেল আর্নিং ও মেইন ব্যালেন্স উভয়ত্রই যোগ করা হচ্ছে
            cursor.execute("UPDATE users SET balance = balance + 0.01 WHERE user_id = ?", (referred_by,))
            conn.commit()
            try:
                bot.send_message(
                    referred_by,
                    f"<tg-emoji emoji-id=\"5321280470460145769\">🎁</tg-emoji> <b>রেফারেল বোনাস!</b>\nআপনার রেফারেল লিংক থেকে একজন নতুন মেম্বার যুক্ত হয়েছেন। আপনি পেয়েছেন <b>0.01 টাকা</b> বোনাস!",
                    parse_mode="HTML"
                )
            except Exception:
                pass
    else:
        cursor.execute("UPDATE users SET first_name = ?, username = ? WHERE user_id = ?", (first_name, username, user_id))
        conn.commit()
    conn.close()

    if not check_user_subscription(user_id):
        not_joined_msg = get_setting_msg('not_joined_msg', f"{pe('warn_icon')} আপনি আমাদের চ্যানেলে Join করেননি!")
        bot.send_message(message.chat.id, not_joined_msg, parse_mode="HTML", reply_markup=get_force_sub_markup())
        return

    welcome_template = get_setting_msg('welcome_msg', f"স্বাগতম {{first_name}}!")
    landing_text = welcome_template.replace("{first_name}", first_name)

    bot.send_message(message.chat.id, landing_text, parse_mode="HTML", reply_markup=main_menu_inline(user_id))
    bot.send_message(message.chat.id, f"{pe('down_arrow')} আপনার সুবিধার্থে নিচের মেনু বাটনগুলো ব্যবহার করুন:", parse_mode="HTML", reply_markup=get_permanent_keyboard(user_id))

@bot.message_handler(func=lambda message: message.text and any(keyword in message.text for keyword in ["All Services", "Deposit", "Profile", "Support", "Get Code", "Referral", "Admin Panel", "Search User ID"]))
def handle_reply_buttons(message):
    update_owner_premium_status(message.from_user)
    user_id = message.from_user.id
    text = message.text
    username = f"@{message.from_user.username}" if message.from_user.username else "N/A"
    
    save_user_id_to_file(user_id)

    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("UPDATE users SET username = ? WHERE user_id = ?", (username, user_id))
    conn.commit()
    conn.close()

    if not check_user_subscription(user_id):
        not_joined_msg = get_setting_msg('not_joined_msg', f"{pe('warn_icon')} আপনি এখনো চ্যানেলে Join করেননি!")
        bot.send_message(message.chat.id, not_joined_msg, parse_mode="HTML", reply_markup=get_force_sub_markup())
        return

    if user_id in user_temp_deposit:
        del user_temp_deposit[user_id]
    
    if "All Services" in text:
        markup = get_categories_markup()
        bot.send_message(message.chat.id, f"{pe('welcome_shop')} <b>আমাদের কাছে নিচের সার্ভিসগুলো রয়েছে:</b>", parse_mode="HTML", reply_markup=markup)

    elif "Deposit" in text:
        user_temp_deposit[user_id] = {"step": "waiting_amount"}
        msg = get_setting_msg('deposit_info_msg', (
            f"{pe('deposit_money')} <b>আপনি কত টাকা ডিপোজিট করতে চান সংখ্যাটি লিখে পাঠান:</b>\n\n"
            f"{pe('list_point')} সর্বনিম্ন ১০ টাকা\n"
            f"{pe('list_point')} সর্বোচ্চ ১০০০০ টাকা"
        ))
        bot.send_message(message.chat.id, msg, parse_mode="HTML", reply_markup=get_deposit_amount_markup())

    elif "Profile" in text:
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT balance, username, COALESCE(referral_deposit_bonus, 0) FROM users WHERE user_id = ?", (user_id,))
        res = cursor.fetchone()
        bal = res[0] if res else 0.0
        u_name = res[1] if res and res[1] else username
        referral_deposit_bonus = res[2] if res else 0.0
        
        cursor.execute("SELECT COUNT(*) FROM users WHERE referred_by = ?", (user_id,))
        ref_count = cursor.fetchone()[0]
        ref_earned = (ref_count * 0.01) + referral_deposit_bonus
        conn.close()
        
        dollar_val = bal / 125.0
        
        profile_text = (
            f"{pe('profile_user')} <b>Your Account Profile</b>\n\n"
            f"{pe('id_badge')} <b>User ID:</b> <code>{user_id}</code>\n"
            f"{pe('username_link')} <b>Username:</b> <b>{u_name}</b>\n"
            f"{pe('balance_coin')} <b>Account Balance:</b> <b>৳{bal}</b> (~${dollar_val:.2f}) {pe('diamond_badge')}\n\n"
            f"<tg-emoji emoji-id=\"5386380500946414098\">👥</tg-emoji> <b>Total Referral:</b> <b>{ref_count} জন</b>\n"
            f"{pe('balance_coin')} <b>Total Referral Bonus:</b> <b>৳{ref_earned:.2f}</b>"
        )
        bot.send_message(message.chat.id, profile_text, parse_mode="HTML")

    elif "Support" in text:
        supp_msg = get_setting_msg('support_msg', f"{pe('support_headphone')} যেকোনো প্রয়োজনে আমাদের সাপোর্ট আইডিতে যোগাযোগ করুন:\nhttps://t.me/FBbuysellAX")
        bot.send_message(message.chat.id, supp_msg, parse_mode="HTML")

    elif "Get Code" in text:
        get_code_url = get_setting_msg('get_code_link', 'https://dongvanfb.net/read_mail_box/')
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Hotmail & Outlook Code", "get_code", url=get_code_url))
        
        get_code_text = f"<tg-emoji emoji-id=\"5321331284218238259\">🔥</tg-emoji> <b>Hotmail, Outlook Receivers Code আনতে চাইলে এই বাটনে ক্লিক করুন:</b>"
        bot.send_message(message.chat.id, get_code_text, parse_mode="HTML", reply_markup=markup)

    elif "Referral" in text:
        bot_info = bot.get_me()
        ref_link = f"https://t.me/{bot_info.username}?start={user_id}"
        ref_text = (
            f"<tg-emoji emoji-id=\"5386380500946414098\">⭐</tg-emoji> <b>Referral System & Earnings</b>\n\n"
            f"<tg-emoji emoji-id=\"5379742233853451967\">📌</tg-emoji> আপনার রেফারেল লিংক:\n<code>{ref_link}</code>\n\n"
            f"{pe('list_point')} কেউ আপনার লিংকে জয়েন করলে পাবেন: <b>0.01 টাকা</b>\n"
            f"{pe('list_point')} আপনার রেফারকৃত কেউ ডিপোজিট করলে পাবেন: <b>0.02 টাকা</b>\n\n"
            f"<tg-emoji emoji-id=\"6258108916136153920\">✨</tg-emoji> লিংকটি বন্ধুদের সাথে শেয়ার করুন!"
        )
        bot.send_message(message.chat.id, ref_text, parse_mode="HTML")

    elif "Search User ID" in text and user_id == ADMIN_ID:
        admin_states[user_id] = {"action": "searching_user"}
        bot.send_message(message.chat.id, f"{pe('list_point')} ইউজারের সম্পূর্ণ তথ্য ও ব্যালেন্স দেখতে তার <b>User ID</b> চ্যাটে লিখে পাঠান:", parse_mode="HTML")

    elif "Admin Panel" in text and user_id == ADMIN_ID:
        bot.send_message(message.chat.id, f"{pe('admin_crown')} <b>Admin Control Panel</b>\n\nনিচের অপশনগুলো থেকে ম্যানেজ করুন:", parse_mode="HTML", reply_markup=get_admin_markup())

def process_purchase(chat_id, user_id, cat_id, qty):
    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("BEGIN IMMEDIATE")
    cursor.execute("SELECT price, name, button_name FROM categories WHERE cat_id = ? AND is_active = 1", (cat_id,))
    cat_data = cursor.fetchone()
    if not cat_data:
        conn.rollback()
        conn.close()
        bot.send_message(chat_id, f"{pe('warn_icon')} এই সার্ভিসটি বর্তমানে আর উপলব্ধ নেই।", parse_mode="HTML")
        return

    price_per_item = cat_data[0]
    cat_name = cat_data[1]
    button_name = cat_data[2] or cat_name
    total_cost = price_per_item * qty

    cursor.execute("SELECT balance FROM users WHERE user_id = ? FOR UPDATE", (user_id,))
    user_balance_row = cursor.fetchone()
    user_balance = user_balance_row[0] if user_balance_row else 0.0

    if user_balance < total_cost:
        conn.rollback()
        conn.close()
        bot.send_message(
            chat_id, 
            f"{pe('insufficient_bal')} <b>আপনার অ্যাকাউন্টে পর্যাপ্ত ব্যালেন্স নেই!</b>\n\n"
            f"{pe('money_spent')} প্রয়োজন: ৳{total_cost}\n"
            f"{pe('wallet_balance')} আপনার আছে: ৳{user_balance}\n\n"
            f"{pe('step_tick')} আগে ডিপোজিট করুন, তারপর পণ্য কিনুন।",
            parse_mode="HTML",
            reply_markup=get_permanent_keyboard(user_id)
        )
        return

    cursor.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
    stock_count = cursor.fetchone()[0]

    if stock_count < qty:
        conn.rollback()
        conn.close()
        bot.send_message(chat_id, f"{pe('no_stock')} দুঃখিত, এই মুহূর্তে পর্যাপ্ত স্টক নেই! স্টকে আছে: <b>{stock_count} পিস</b>።", parse_mode="HTML")
        return

    cursor.execute("SELECT id, content FROM stock WHERE cat_id = ? AND status = 'available' ORDER BY id ASC LIMIT ? FOR UPDATE", (cat_id, qty))
    items = cursor.fetchall()
    if len(items) < qty:  # another buyer took the stock between the COUNT and the locked SELECT
        conn.rollback()
        conn.close()
        bot.send_message(chat_id, f"{pe('no_stock')} দুঃখিত, এই মুহূর্তে পর্যাপ্ত স্টক নেই! স্টকে আছে: <b>{len(items)} পিস</b>।", parse_mode="HTML")
        return

    new_balance = user_balance - total_cost
    order_key = str(uuid.uuid4())[:8]
    sold_at = datetime.now(timezone.utc).isoformat()
    cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (new_balance, user_id))

    for item_id, content in items:
        cursor.execute(
            "UPDATE stock SET status = 'sold', sold_by = ?, sold_at = ?, order_id = ? WHERE id = ? AND status = 'available'",
            (user_id, sold_at, order_key, item_id)
        )
        cursor.execute(
            "INSERT OR IGNORE INTO stock_sales (stock_id, cat_id, category_name, button_name, buyer_user_id, item_content, unit_price, order_id, sold_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (item_id, cat_id, cat_name, button_name, user_id, content, price_per_item, order_key, sold_at)
        )

    conn.commit()
    conn.close()

    raw_contents = [content.strip() for item_id, content in items]
    order_delivery_cache[order_key] = {
        "items": raw_contents,
        "cat_name": cat_name,
        "qty": qty,
        "cat_id": cat_id
    }

    delivery_markup = InlineKeyboardMarkup(row_width=2)
    delivery_markup.add(
        premium_inline_button("Open Here", "open_here_btn", callback_data=f"show_open_{order_key}"),
        premium_inline_button("TXT File", "txt_file_btn", callback_data=f"show_txt_{order_key}")
    )

    purchase_msg = (
        f"{pe('buy_success')} <b>Purchase Successful!</b>\n\n"
        f"{pe('box_package')} Item: <b>{cat_name}</b>\n"
        f"{pe('quantity_icon')} Quantity: <b>{qty} Pcs</b>\n"
        f"{pe('money_spent')} Total Cost: <b>৳{total_cost}</b>\n"
        f"{pe('wallet_balance')} Remaining Balance: <b>৳{new_balance}</b>\n\n"
        f"{pe('choose_select')} <b>আপনার ফাইলটি বট থেকে নিতে চাচ্ছেন নাকি TXT ফাইল আকারে নিতে চাচ্ছেন সিলেক্ট করুন:</b>"
    )

    bot.send_message(chat_id, purchase_msg, parse_mode="HTML", reply_markup=delivery_markup)

@bot.callback_query_handler(func=lambda call: True)
def handle_callback(call):
    update_owner_premium_status(call.from_user)
    user_id = call.from_user.id
    username = f"@{call.from_user.username}" if call.from_user.username else "N/A"
    save_user_id_to_file(user_id)

    if _handle_gateway_callback(call, user_id):
        return

    if call.data.startswith("show_open_"):
        order_key = call.data.replace("show_open_", "")
        if order_key in order_delivery_cache:
            data = order_delivery_cache[order_key]
            items = data["items"]
            cat_name = data["cat_name"]
            formatted_items = [f"{idx}. <code>{content}</code>" for idx, content in enumerate(items, 1)]
            open_msg = f"{pe('buy_success')} <b>{cat_name} (Total: {len(items)} Pcs)</b>\n\n{pe('copy_down')} <b>ক্লিক করে কপি করুন:</b>\n\n" + "\n\n".join(formatted_items)
            bot.send_message(call.message.chat.id, open_msg, parse_mode="HTML")
            bot.answer_callback_query(call.id, "অ্যাকাউন্টগুলো নিচে ওপেন হয়েছে!")
        else:
            bot.answer_callback_query(call.id, "এই অর্ডারের সেশনটি মেয়াদোত্তীর্ণ হয়ে গেছে।", show_alert=True)
        return

    elif call.data.startswith("show_txt_"):
        order_key = call.data.replace("show_txt_", "")
        if order_key in order_delivery_cache:
            data = order_delivery_cache[order_key]
            items, cat_name, cat_id = data["items"], data["cat_name"], data["cat_id"]
            file_path = f"{cat_id}_order.txt"
            with open(file_path, "w", encoding="utf-8") as f:
                f.write("\n".join(items))
            with open(file_path, "rb") as f:
                bot.send_document(call.message.chat.id, f, caption=f"{pe('txt_file_caption')} <b>{cat_name}</b> এর টেক্সট ফাইল নিচে দেওয়া হলো:", parse_mode="HTML")
            os.remove(file_path)
            bot.answer_callback_query(call.id, "ফাইল পাঠানো হয়েছে!")
        else:
            bot.answer_callback_query(call.id, "এই অর্ডারের সেশনটি মেয়াদোত্তীর্ণ হয়ে গেছে।", show_alert=True)
        return

    if call.data == "verify_subscription":
        if check_user_subscription(user_id):
            conn = db_connect()
            cursor = conn.cursor()
            cursor.execute("SELECT user_id FROM users WHERE user_id = ?", (user_id,))
            if not cursor.fetchone():
                cursor.execute("INSERT INTO users (user_id, first_name, balance, username) VALUES (?, ?, 0.0, ?)", (user_id, call.from_user.first_name or "User", username))
            else:
                cursor.execute("UPDATE users SET username = ? WHERE user_id = ?", (username, user_id))
            conn.commit()
            conn.close()

            try: bot.delete_message(call.message.chat.id, call.message.message_id)
            except Exception: pass

            bot.send_message(call.message.chat.id, f"{pe('step_tick')} আপনার একাউন্ট সফলভাবে Verify হয়েছে!\nএখন আপনি বটের সকল ফিচার ও কেনাকাটা করতে পারবেন। নিচে আপনার মেনু দেওয়া হলো:", parse_mode="HTML", reply_markup=get_permanent_keyboard(user_id))
        else:
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} আপনি এখনো চ্যানেলে Join করেননি! আগে চ্যানেলে জয়েন করুন তারপর Verify ক্লিক করুন।", parse_mode="HTML")
        return

    if not check_user_subscription(user_id):
        bot.send_message(call.message.chat.id, f"{pe('warn_icon')} আগে আমাদের চ্যানেলে Join করুন এবং Verify করুন!", parse_mode="HTML", reply_markup=get_force_sub_markup())
        return

    if call.data == "all_services":
        markup = get_categories_markup()
        try:
            bot.edit_message_text(f"{pe('welcome_shop')} <b>আমাদের কাছে নিচের সার্ভিসগুলো রয়েছে:</b>", call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, f"{pe('welcome_shop')} <b>আমাদের কাছে নিচের সার্ভিসগুলো রয়েছে:</b>", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "group_mail":
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT cat_id, name, price, has_emoji FROM categories WHERE group_type = 'mail' AND is_active = 1 "
                       "ORDER BY CASE cat_id WHEN 'hotmail' THEN 1 WHEN 'outlook' THEN 2 WHEN 'Outlook fr' THEN 3 ELSE 99 END, created_at, name COLLATE NOCASE")
        mail_cats = cursor.fetchall()
        conn.close()

        markup = InlineKeyboardMarkup(row_width=1)
        for cat_id, name, price, has_em in mail_cats:
            sub_conn = db_connect()
            sub_cur = sub_conn.cursor()
            sub_cur.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
            stock_count = sub_cur.fetchone()[0]
            sub_conn.close()
            em_key = get_category_button_emoji_key(cat_id, name, "mail", has_em)
            markup.add(premium_inline_button(f"{name} - ৳{price} (Stock: {stock_count})", em_key, callback_data=f"buy_{cat_id}"))
        markup.add(premium_inline_button("Back", "back_button", callback_data="all_services"))

        try:
            bot.edit_message_text(f"{pe('mail_cat')} <b>Mail Service</b> {pe('mail_cat')}\n\nনিচের মেইলগুলো থেকে আপনার পছন্দমতো সিলেক্ট করুন:", call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, f"{pe('mail_cat')} <b>Mail Service</b> {pe('mail_cat')}\n\nনিচের মেইলগুলো থেকে আপনার পছন্দমতো সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "group_proxy":
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT cat_id, name, price, has_emoji FROM categories WHERE group_type = 'proxy' AND is_active = 1 "
                       "ORDER BY CASE cat_id WHEN 'proxy_9_100' THEN 1 WHEN 'proxy' THEN 2 WHEN 'proxy_711_100' THEN 3 "
                       "WHEN 'proxy_711_200' THEN 4 WHEN 'proxy_h143_100' THEN 5 WHEN 'proxy_h143_200' THEN 6 "
                       "WHEN 'proxy_rapid_100' THEN 7 WHEN 'proxy_rapid_200' THEN 8 WHEN 'proxy_loki_100' THEN 9 ELSE 99 END, created_at, name COLLATE NOCASE")
        proxy_cats = cursor.fetchall()
        conn.close()

        markup = InlineKeyboardMarkup(row_width=1)
        for cat_id, name, price, has_em in proxy_cats:
            sub_conn = db_connect()
            sub_cur = sub_conn.cursor()
            sub_cur.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
            stock_count = sub_cur.fetchone()[0]
            sub_conn.close()
            em_key = get_category_button_emoji_key(cat_id, name, "proxy", has_em)
            markup.add(premium_inline_button(f"{name} - ৳{price} (Stock: {stock_count})", em_key, callback_data=f"buy_{cat_id}"))
        markup.add(premium_inline_button("Back", "back_button", callback_data="all_services"))

        try:
            bot.edit_message_text(f"{pe('proxy_cat')} <b>Proxy Service</b> {pe('proxy_cat')}\n\nনিচের প্রক্সিগুলো থেকে আপনার পছন্দমতো সিলেক্ট করুন:", call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, f"{pe('proxy_cat')} <b>Proxy Service</b> {pe('proxy_cat')}\n\nনিচের প্রক্সিগুলো থেকে আপনার পছন্দমতো সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "special_cat_telegram_premium":
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT sub_id, sub_name, price, has_emoji FROM sub_services WHERE cat_id = 'telegram_premium'")
        sub_items = cursor.fetchall()
        conn.close()

        markup = InlineKeyboardMarkup(row_width=1)
        for sub_id, sub_name, price, has_em in sub_items:
            em_key = get_sub_service_button_emoji_key(sub_id, has_em, "telegram_premium_cat")
            markup.add(premium_inline_button(f"{sub_name} - ৳{price}", em_key, callback_data=f"subbuy_{sub_id}"))
        markup.add(premium_inline_button("Back", "back_button", callback_data="all_services"))

        try:
            bot.edit_message_text(f"{pe('telegram_premium_cat')} <b>Telegram Premium Buy</b> {pe('telegram_premium_cat')}\n\nনিচের প্যাকেজগুলো থেকে আপনার পছন্দমতো সিলেক্ট করুন:", call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, f"{pe('telegram_premium_cat')} <b>Telegram Premium Buy</b> {pe('telegram_premium_cat')}\n\nনিচের প্যাকেজগুলো থেকে আপনার পছন্দমতো সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "special_cat_vpn_service":
        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            premium_inline_button("3 Day", "vpn_service_cat", callback_data="vpn_dur_vpn_3d"),
            premium_inline_button("7 Day", "vpn_service_cat", callback_data="vpn_dur_vpn_7d"),
            premium_inline_button("14 Day", "vpn_service_cat", callback_data="vpn_dur_vpn_14d"),
            premium_inline_button("30 Day", "vpn_service_cat", callback_data="vpn_dur_vpn_30d"),
            premium_inline_button("Back", "back_button", callback_data="all_services")
        )
        try:
            bot.edit_message_text(f"{pe('vpn_service_cat')} <b>VPN Service</b> {pe('vpn_service_cat')}\n\nআপনি কতদিনের জন্য VPN নিতে চাচ্ছেন মেয়াদের ক্যাটাগরি সিলেক্ট করুন:", call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, f"{pe('vpn_service_cat')} <b>VPN Service</b> {pe('vpn_service_cat')}\n\nআপনি কতদিনের জন্য VPN নিতে চাচ্ছেন মেয়াদের ক্যাটাগরি সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("vpn_dur_"):
        dur_cat = call.data.replace("vpn_dur_", "")
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT sub_id, sub_name, price, has_emoji FROM sub_services WHERE cat_id = ?", (dur_cat,))
        sub_items = cursor.fetchall()
        conn.close()

        dur_text_map = {
            "vpn_3d": "৩ দিন মেয়াদের VPN গুলো নিচে দেওয়া হলো:",
            "vpn_7d": "৭ দিন মেয়াদের VPN গুলো নিচে দেওয়া হলো:",
            "vpn_14d": "১৪ দিন মেয়াদের VPN গুলো নিচে দেওয়া হলো:",
            "vpn_30d": "৩০ দিন মেয়াদের VPN গুলো নিচে দেওয়া হলো:"
        }
        dynamic_heading = dur_text_map.get(dur_cat, "নিচের VPN গুলো থেকে আপনার পছন্দের সার্ভিসটি সিলেক্ট করুন:")

        if not sub_items:
            bot.answer_callback_query(call.id, "এই মেয়াদের ভিপিএন বর্তমানে স্টকে নেই!", show_alert=True)
            return

        markup = InlineKeyboardMarkup(row_width=1)
        for sub_id, sub_name, price, has_em in sub_items:
            em_key = get_sub_service_button_emoji_key(sub_id, has_em, get_vpn_emoji_key(sub_name))
            markup.add(premium_inline_button(f"{sub_name} - ৳{price}", em_key, callback_data=f"subbuy_{sub_id}"))
        markup.add(premium_inline_button("Back", "back_button", callback_data="special_cat_vpn_service"))

        try:
            bot.edit_message_text(f"{pe('vpn_service_cat')} <b>VPN Packages</b>\n\n{dynamic_heading}", call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, f"{pe('vpn_service_cat')} <b>VPN Packages</b>\n\n{dynamic_heading}", parse_mode="HTML", reply_markup=markup)
        return

    if call.data.startswith("depamt_"):
        amt = float(call.data.split("_")[1])
        user_temp_deposit[user_id] = {"amount": amt, "step": "waiting_method"}
        bot.send_message(call.message.chat.id, f"{pe('sendmoney_shield')} <b>আপনি কিসের মাধ্যমে পেমেন্ট করতে চাচ্ছেন সিলেক্ট করুন:</b>", parse_mode="HTML", reply_markup=get_payment_method_markup())
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        return

    if call.data.startswith("paymethod_"):
        method = call.data.split("_")[1]
        amt = user_temp_deposit.get(user_id, {}).get("amount", 10.0)
        user_temp_deposit[user_id] = {
            "amount": amt,
            "method": method,
            "step": "waiting_trx"
        }
        
        if method == "Binance" and pgw.merchant_configured():
            _gw_start_binance_order(call, user_id, amt)
            try: bot.delete_message(call.message.chat.id, call.message.message_id)
            except Exception: pass
            return

        if method == "Binance":
            binance_uid = os.environ.get("BINANCE_PAY_ID") or get_setting_msg('binance_uid', '1123474021')
            dollar_amount = amt / 125.0
            msg = (
                f"{pe('binance_method')} আপনি <b>Binance</b> সিলেক্ট করেছেন।\n\n"
                f"<tg-emoji emoji-id=\"5463424023734014980\">🪙</tg-emoji> এই Binance User ID-তে ডলার সেন্ড করুন:\n"
                f"<tg-emoji emoji-id=\"5798751138647905130\">➡️</tg-emoji>Pay UID: <code>{binance_uid}</code>\n\n"
                f"{pe('deposit_money')} Send: <b>${dollar_amount:.2f} Binance USD</b> (৳{int(amt) if amt.is_integer() else amt})\n"
                f"<i>(১ ডলার = ১২৫ টাকা অনুযায়ী নির্ধারিত)</i>\n\n"
                f"{pe('trx_input')} ডলার পাঠানোর পর আপনার ট্রানজেকশন আইডি (Transaction ID) চ্যাটে লিখে পাঠান:"
            )
        else:
            number_map = {
                "bKash": get_setting_msg('bkash_num', '+8801842145918'),
                "Nagad": get_setting_msg('nagad_num', '+8801842145918'),
                "Rocket": get_setting_msg('rocket_num', '+8801842145918')
            }
            pay_num = number_map.get(method, "+8801842145918")
            method_pe_key = "bkash_method" if method == "bKash" else ("nagad_method" if method == "Nagad" else "rocket_method")

            msg = (
                f"{pe(method_pe_key)} আপনি <b>{method}</b> সিলেক্ট করেছেন।\n\n"
                f"{pe('sendmoney_shield')} পার্সোনাল নাম্বারে টাকা সেন্ড মানি করুন:\n"
                f"{pe(method_pe_key)} {method}: <code>{pay_num}</code>\n\n"
                f"{pe('deposit_money')} <b>{int(amt) if amt.is_integer() else amt} TK Send Money</b>\n\n"
                f"{pe('trx_input')} টাকা পাঠানোর পর আপনার ট্রানজেকশন আইডি (Transaction ID) চ্যাটে লিখে পাঠান:"
            )
        bot.send_message(call.message.chat.id, msg, parse_mode="HTML")
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        return

    # Telegram Member Sell callbacks are deliberately handled before the existing
    # generic service/admin callback code so the other four services remain unchanged.
    if call.data == "member_sell":
        markup = InlineKeyboardMarkup(row_width=1)
        markup.add(
            premium_inline_button("30 Day Members", MEMBER_SELL_EMOJIS["duration"], callback_data="ms_duration_30"),
            premium_inline_button("3 Month Members", MEMBER_SELL_EMOJIS["duration"], callback_data="ms_duration_90"),
            premium_inline_button("1 Year Members", MEMBER_SELL_EMOJIS["duration"], callback_data="ms_duration_365"),
            premium_inline_button("Back", "back_button", callback_data="all_services")
        )
        heading = (
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>Telegram Member Sell</b>\n\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['menu_description'])} আপনার প্রয়োজন অনুযায়ী মেম্বার সার্ভিসের মেয়াদ সিলেক্ট করুন।"
        )
        try:
            bot.edit_message_text(heading, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, heading, parse_mode="HTML", reply_markup=markup)
        bot.answer_callback_query(call.id)
        return

    if call.data.startswith("ms_duration_"):
        duration_key = call.data.replace("ms_duration_", "", 1)
        plan = MEMBER_SELL_PLANS.get(duration_key)
        if not plan:
            bot.answer_callback_query(call.id, "সার্ভিসটি পাওয়া যায়নি।", show_alert=True)
            return

        markup = InlineKeyboardMarkup(row_width=1)
        for quantity, price in plan["packages"]:
            qty_label = f"{quantity // 1000}k" if quantity >= 1000 else str(quantity)
            markup.add(premium_inline_button(
                f"{qty_label} Members = {price} Tk",
                MEMBER_SELL_EMOJIS["service"],
                callback_data=f"ms_package_{duration_key}_{quantity}"
            ))
        markup.add(premium_inline_button("Back", "back_button", callback_data="member_sell"))

        heading = (
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['duration'])} <b>{html.escape(plan['heading'])}</b>\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['delivery'])} <b>Delivery Time - {html.escape(plan['delivery'])}</b>\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['fast'])} <b>Fast Delivery and Best Member</b>\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['down'])} <b>নিচের সার্ভিসে ক্লিক করুন</b>"
        )
        try:
            bot.edit_message_text(heading, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception:
            bot.send_message(call.message.chat.id, heading, parse_mode="HTML", reply_markup=markup)
        bot.answer_callback_query(call.id)
        return

    if call.data.startswith("ms_package_"):
        parts = call.data.split("_")
        if len(parts) != 4:
            bot.answer_callback_query(call.id, "প্যাকেজের তথ্য সঠিক নয়।", show_alert=True)
            return
        duration_key, quantity_text = parts[2], parts[3]
        plan = MEMBER_SELL_PLANS.get(duration_key)
        try:
            quantity = int(quantity_text)
            price = next((amount for count, amount in plan["packages"] if count == quantity), None) if plan else None
        except (TypeError, ValueError):
            price = None
        if price is None:
            bot.answer_callback_query(call.id, "এই প্যাকেজটি পাওয়া যায়নি।", show_alert=True)
            return

        member_sell_states[user_id] = {
            "step": "waiting_target_link",
            "duration_key": duration_key,
            "duration_label": plan["label"],
            "quantity": quantity,
            "price": float(price),
        }
        qty_label = f"{quantity // 1000}k" if quantity >= 1000 else str(quantity)
        prompt = (
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>আপনার প্যাকেজ:</b> {html.escape(plan['label'])} Members\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_members'])} <b>মেম্বার:</b> {qty_label} জন\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_price'])} <b>মূল্য:</b> ৳{price}\n\n"
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_target'])} আপনি যে চ্যানেল বা গ্রুপে মেম্বার নিতে চাচ্ছেন, সেই চ্যানেল/গ্রুপের Username অথবা Link এখানে পেস্ট করুন।"
        )
        try:
            bot.edit_message_text(prompt, call.message.chat.id, call.message.message_id, parse_mode="HTML")
        except Exception:
            bot.send_message(call.message.chat.id, prompt, parse_mode="HTML")
        bot.answer_callback_query(call.id)
        return

    if call.data.startswith("ms_complete_") and user_id == ADMIN_ID:
        order_id = call.data.replace("ms_complete_", "", 1)
        conn = db_connect()
        cur = conn.cursor()
        cur.execute("BEGIN IMMEDIATE")
        cur.execute("SELECT user_id, status FROM member_sell_orders WHERE order_id = ?", (order_id,))
        row = cur.fetchone()
        if not row or row[1] != "pending":
            conn.rollback()
            conn.close()
            bot.answer_callback_query(call.id, "এই অর্ডারটি ইতিমধ্যে প্রসেস করা হয়েছে।", show_alert=True)
            return
        cur.execute(
            "UPDATE member_sell_orders SET status = 'delivering' WHERE order_id = ? AND status = 'pending'",
            (order_id,)
        )
        if cur.rowcount != 1:
            conn.rollback()
            conn.close()
            bot.answer_callback_query(call.id, "অর্ডারটি প্রসেস করা যাচ্ছে না।", show_alert=True)
            return
        conn.commit()
        conn.close()
        admin_states[user_id] = {"action": "waiting_member_sell_delivery", "order_id": order_id, "target_user": row[0]}
        try:
            bot.edit_message_text(
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} <b>ডেলিভারি প্রস্তুত হচ্ছে</b>\nOrder ID: <code>{html.escape(order_id)}</code>",
                call.message.chat.id, call.message.message_id, parse_mode="HTML"
            )
        except Exception:
            pass
        bot.send_message(
            call.message.chat.id,
            f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} অর্ডার <code>{html.escape(order_id)}</code>-এর জন্য যে ডেলিভারি মেসেজটি কাস্টমারের কাছে পাঠাতে চান, সেটি লিখে পাঠান:",
            parse_mode="HTML"
        )
        bot.answer_callback_query(call.id, "ডেলিভারি মেসেজের অপেক্ষায় আছে।")
        return

    if call.data.startswith("ms_refund_") and user_id == ADMIN_ID:
        order_id = call.data.replace("ms_refund_", "", 1)
        conn = db_connect()
        cur = conn.cursor()
        cur.execute("BEGIN IMMEDIATE")
        cur.execute(
            "SELECT user_id, price, status FROM member_sell_orders WHERE order_id = ?",
            (order_id,)
        )
        row = cur.fetchone()
        if not row or row[2] != "pending":
            conn.rollback()
            conn.close()
            bot.answer_callback_query(call.id, "এই অর্ডারটি ইতিমধ্যে প্রসেস করা হয়েছে।", show_alert=True)
            return
        target_user, refund_amount, status = row
        cur.execute(
            "UPDATE member_sell_orders SET status = 'refunded', refunded_at = ? WHERE order_id = ? AND status = 'pending'",
            (datetime.now(timezone.utc).isoformat(), order_id)
        )
        if cur.rowcount != 1:
            conn.rollback()
            conn.close()
            bot.answer_callback_query(call.id, "রিফান্ডটি সম্পন্ন করা যায়নি; আবার যাচাই করুন।", show_alert=True)
            return
        cur.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (refund_amount, target_user))
        conn.commit()
        conn.close()

        try:
            bot.send_message(
                target_user,
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['refund_notice'])} <b>দুঃখিত, বর্তমানে এই সার্ভিসটি দেওয়া যাচ্ছে না। আপনি অন্য কিছু ট্রাই করেন।</b>\n\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['refund_amount'])} আপনার কাটা ৳{refund_amount:g} টাকা আপনার অ্যাকাউন্টে ফেরত দেওয়া হয়েছে।",
                parse_mode="HTML",
                reply_markup=get_permanent_keyboard(target_user)
            )
        except Exception as e:
            bot.send_message(ADMIN_ID, f"Refund completed, but user notification failed (User ID: <code>{target_user}</code>): <code>{html.escape(str(e))}</code>", parse_mode="HTML")
        try:
            bot.edit_message_text(
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['refund_notice'])} <b>Telegram Member Sell — No Delivery / Refunded</b>\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['success_order_id'])} Order ID: <code>{html.escape(order_id)}</code>\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['refund_amount'])} Refund: ৳{refund_amount:g}",
                call.message.chat.id, call.message.message_id, parse_mode="HTML"
            )
        except Exception:
            pass
        bot.answer_callback_query(call.id, "অর্ডার রিফান্ড করা হয়েছে।", show_alert=True)
        return

    conn = db_connect()
    cursor = conn.cursor()

    if call.data == "admin_main":
        if user_id in admin_states: del admin_states[user_id]
        conn.close()
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('admin_crown')} <b>Admin Control Panel</b>\n\nনিচের অপশনগুলো থেকে ম্যানেজ করুন:", parse_mode="HTML", reply_markup=get_admin_markup())
        return

    elif call.data == "admin_auto_member_count" and user_id == ADMIN_ID:
        cursor.execute("SELECT user_id FROM users")
        db_users = cursor.fetchall()
        conn.close()
        
        all_unique_ids = set()
        for u in db_users:
            all_unique_ids.add(str(u[0]))
            
        if os.path.exists(USER_LOG_FILE):
            with open(USER_LOG_FILE, "r", encoding="utf-8") as f:
                for line in f:
                    cleaned = line.strip()
                    if cleaned: all_unique_ids.add(cleaned)
                    
        with open(USER_LOG_FILE, "w", encoding="utf-8") as f:
            for uid in sorted(all_unique_ids):
                f.write(f"{uid}\n")
                
        if all_unique_ids:
            with open(USER_LOG_FILE, "rb") as f:
                bot.send_document(call.message.chat.id, f, caption=f"{pe('box_package')} <b>auto_member_count_user.txt</b>\nমোট মেম্বার সংখ্যা: <b>{len(all_unique_ids)} জন</b>", parse_mode="HTML")
            bot.answer_callback_query(call.id, "ফাইল পাঠানো হয়েছে!")
        else:
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} এখনো কোনো মেম্বারের ইউজার আইডি সেভ হয়নি।", parse_mode="HTML")
        return

    elif call.data == "admin_broadcast" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_direct_broadcast_message"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(
            call.message.chat.id,
            f"{pe('loudspeaker')} <b>Broadcast Message</b>\n\nআপনি যে মেসেজ/ছবি/ভিডিও/ফাইল/ভয়েস পাঠাবেন, সেটাই সরাসরি সকল registered user-এর কাছে পাঠানো হবে।",
            parse_mode="HTML",
            reply_markup=markup
        )
        return

    elif call.data == "admin_premium_emoji_set" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_premium_emoji_txt"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(
            call.message.chat.id,
            f"{pe('button_edit')} <b>Premium Emoji Set</b>\n\nএকটি <code>.txt</code> ফাইল upload করুন অথবা সরাসরি এই ফরম্যাটে লিখে পাঠান: <code>🔴 = 5788939937335366</code>",
            parse_mode="HTML",
            reply_markup=markup
        )
        return

    elif call.data == "admin_payment_method_edit" and user_id == ADMIN_ID:
        conn.close()
        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            premium_inline_button("Edit bKash", "edit_service", callback_data="editpay_bkash"),
            premium_inline_button("Edit Nagad", "edit_service", callback_data="editpay_nagad"),
            premium_inline_button("Edit Rocket", "edit_service", callback_data="editpay_rocket"),
            premium_inline_button("Edit Binance", "edit_service", callback_data="editpay_binance"),
            premium_inline_button("Back", "back_button", callback_data="admin_main")
        )
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('edit_service')} <b>Payment Method Edit</b>\nকোন পেমেন্ট মেথড এডিট করতে চান সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("editpay_") and user_id == ADMIN_ID:
        pmethod = call.data.replace("editpay_", "")
        conn.close()
        admin_states[user_id] = {"action": "saving_payment_number", "method": pmethod}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_payment_method_edit"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('edit_pencil')} <b>{pmethod.upper()}</b> এর জন্য নতুন নাম্বার বা ইউআইডি (UID) লিখে পাঠান:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_pc_directory_setup" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_pc_directory_path"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('download_txt')} পিসির ফোল্ডার পাথ (Directory Path) লিখে পাঠান যেখানে এনালাইসিস ফাইল সেভ হবে:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_pc_live_money_setup" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_pc_live_money_path"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('download_txt')} পিসির লাইভ মানি ফোল্ডার পাথ লিখে পাঠান:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_pc_live_stock_setup" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_pc_live_stock_path"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('download_txt')} পিসির লাইভ স্টক ফোল্ডার পাথ লিখে পাঠান:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_live_broadcast" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_analysis_txt_for_broadcast"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('loudspeaker')} <b>Live Analysis & User Broadcast Message</b>\n\nবট এনালাইসিস বা <code>auto_member_count_user.txt</code> ফাইলটি সরাসরি এখানে ফাইল আকারে পাঠান:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_add_member_balance" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_member_uid_for_balance"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('add_balance')} <b>Add Member Money Back</b>\n\nযে ইউজারের অ্যাকাউন্টে টাকা ব্যাক দিতে চাচ্ছেন, তার সঠিক <b>User ID</b> চ্যাটে লিখে পাঠান:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_remove_member_balance" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_member_uid_for_remove_money"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('remove_money')} <b>Remove Money</b>\n\nযে ইউজারের অ্যাকাউন্ট থেকে টাকা কাট বা এডিট করতে চান, তার সঠিক <b>User ID</b> চ্যাটে লিখে পাঠান:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_bulk_money_update" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_bulk_money_data"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('bulk_update')} <b>Update Back All Money Member</b>\n\nআপনার আগের ডাউনলোড করা ব্যালেন্স লিস্ট ফাইলটি এখানে আপলোড করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("subbuy_"):
        sub_id = call.data.split("_")[1]
        cursor.execute("SELECT cat_id, sub_name, price FROM sub_services WHERE sub_id = ?", (sub_id,))
        sub_data = cursor.fetchone()
        conn.close()

        if not sub_data:
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} দুঃখিত, এই প্যাকেজটি পাওয়া যায়নি।", parse_mode="HTML")
            return

        cat_id, sub_name, price = sub_data
        conn = db_connect()
        cursor = conn.cursor()
        cursor.execute("SELECT balance FROM users WHERE user_id = ?", (user_id,))
        bal_res = cursor.fetchone()
        user_bal = bal_res[0] if bal_res else 0.0
        conn.close()

        if user_bal < price:
            bot.send_message(call.message.chat.id, f"{pe('insufficient_bal')} পর্যাপ্ত ব্যালেন্স নেই! প্রয়োজন ৳{price}, আপনার আছে ৳{user_bal}।", parse_mode="HTML")
            return

        user_temp_deposit[user_id] = {"step": "waiting_service_username", "cat_id": cat_id, "sub_name": sub_name, "price": price}
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass

        emoji_k = "telegram_premium_cat" if "telegram" in cat_id else get_vpn_emoji_key(sub_name)
        bot.send_message(call.message.chat.id, f"{pe(emoji_k)} আপনি সিলেক্ট করেছেন: <b>{sub_name}</b> (মূল্য: ৳{price}) {pe(emoji_k)}\n\n{pe('list_point')} এখন যে আইডিতে সার্ভিস নিতে চাচ্ছেন, সেটির সঠিক <b>Telegram Username</b> বা প্রোফাইল আইডি চ্যাটে লিখে পাঠান:", parse_mode="HTML")
        return

    elif call.data.startswith("buy_"):
        cat_id = call.data.replace("buy_", "")
        cursor.execute("SELECT name, price, group_type FROM categories WHERE cat_id = ? AND is_active = 1", (cat_id,))
        cat = cursor.fetchone()
        cursor.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
        stock_count_res = cursor.fetchone()
        stock_count = stock_count_res[0] if stock_count_res else 0
        conn.close()

        if stock_count == 0 or not cat:
            bot.send_message(call.message.chat.id, f"{pe('no_stock')} দুঃখিত! এই মুহূর্তে এই আইটেমের স্টক শেষ।", parse_mode="HTML")
            return

        back_target = f"group_{cat[2]}" if cat[2] in ('mail', 'proxy') else "all_services"

        user_temp_deposit[user_id] = {"step": "waiting_custom_qty", "cat_id": cat_id}
        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            premium_inline_button("1 Pcs", "qty_select", callback_data=f"qty_{cat_id}_1"),
            premium_inline_button("5 Pcs", "qty_select", callback_data=f"qty_{cat_id}_5"),
            premium_inline_button("10 Pcs", "qty_select", callback_data=f"qty_{cat_id}_10"),
            premium_inline_button("Back", "back_button", callback_data=back_target)
        )
        msg_text = f"{pe('box_package')} <b>{cat[0]}</b>\n{pe('money_spent')} Price: ৳{cat[1]}\nStock: {stock_count} Pcs\n\nSelect quantity:\n{pe('list_point')} অধিক নিতে চাইলে নিচে চ্যাটে কাঙ্ক্ষিত পিস সংখ্যা লিখে পাঠান."
        try: bot.edit_message_text(msg_text, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception: bot.send_message(call.message.chat.id, msg_text, parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("qty_"):
        parts = call.data.split("_")
        qty_str, cat_id = parts[-1], "_".join(parts[1:-1])
        conn.close()
        if user_id in user_temp_deposit and user_temp_deposit[user_id].get("step") == "waiting_custom_qty":
            del user_temp_deposit[user_id]
        process_purchase(call.message.chat.id, user_id, cat_id, int(qty_str))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        return

    elif call.data.startswith("btn_emojichoice_") and user_id == ADMIN_ID:
        choice = call.data.split("_")[2]
        state_data = admin_states.get(user_id, {})
        pending_data = state_data.get("pending_btn_data")
        if not pending_data:
            conn.close()
            bot.answer_callback_query(call.id, "এডিট/অ্যাড সেশনটি পাওয়া যায়নি। আবার শুরু করুন।", show_alert=True)
            return

        if choice == "other":
            admin_states[user_id]["action"] = "waiting_other_emoji_code"
            bot.edit_message_text(
                f"{pe('edit_pencil')} অনুগ্রহ করে প্রিমিয়াম ইমোজির <b>Custom Emoji ID</b> চ্যাটে লিখে পাঠান:",
                call.message.chat.id,
                call.message.message_id,
                parse_mode="HTML"
            )
            conn.close()
            return

        if choice not in ("yes", "no"):
            conn.close()
            bot.answer_callback_query(call.id, "সঠিক Emoji Option নির্বাচন করুন।", show_alert=True)
            return

        try:
            saved_id = _save_pending_button(pending_data, has_emoji=(choice == "yes"))
            del admin_states[user_id]
            label = "প্রিমিয়াম ইমোজিসহ" if choice == "yes" else "ইমোজি ছাড়া"
            bot.send_message(
                call.message.chat.id,
                f"{pe('step_tick')} বাটনটি সফলভাবে {label} সেভ হয়েছে!\n"
                f"নাম: <b>{html.escape(str(pending_data.get('name', '')))}</b>\n"
                f"রেট: <b>৳{float(pending_data.get('price', 0)):g}</b>",
                parse_mode="HTML"
            )
        except Exception as e:
            print(f"Button save error: {e}")
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} বাটনটি সেভ করা যায়নি: <code>{html.escape(str(e))}</code>", parse_mode="HTML")
        conn.close()
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        return

    elif call.data == "admin_add_stock_menu" and user_id == ADMIN_ID:
        if user_id in admin_states: del admin_states[user_id]
        cursor.execute("SELECT cat_id, name FROM categories WHERE is_active = 1")
        categories = cursor.fetchall()
        conn.close()
        markup = InlineKeyboardMarkup(row_width=1)
        for cat_id, name in categories:
            sub_conn = db_connect()
            sub_cur = sub_conn.cursor()
            sub_cur.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
            s_count = sub_cur.fetchone()[0]
            sub_conn.close()
            markup.add(premium_inline_button(f"{name} (Stock: {s_count} Pcs)", "manage_stock", callback_data=f"manage_stock_{cat_id}"))
        
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('box_package')} <b>Stock Management:</b>\nযে সার্ভিসের স্টক ম্যানেজ করতে চান তা সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("manage_stock_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("manage_stock_", "")
        cursor.execute("SELECT name FROM categories WHERE cat_id = ?", (cat_id,))
        cat_res = cursor.fetchone()
        cat_name = cat_res[0] if cat_res else cat_id

        cursor.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
        stock_count = cursor.fetchone()[0]
        conn.close()

        markup = InlineKeyboardMarkup(row_width=1)
        markup.add(
            premium_inline_button("Add New Stock File (.txt)", "add_balance", callback_data=f"select_stock_{cat_id}"),
            premium_inline_button("Download Current Stock (.txt)", "download_txt", callback_data=f"download_stock_{cat_id}"),
            premium_inline_button(f"Remove All Stock ({stock_count} Pcs)", "delete_trash", callback_data=f"clear_stock_{cat_id}"),
            premium_inline_button("Back", "back_button", callback_data="admin_add_stock_menu")
        )
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('box_package')} <b>Stock Management:</b> {cat_name}\nবর্তমান স্টক সংখ্যা: <b>{stock_count} পিস</b>", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("download_stock_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("download_stock_", "")
        cursor.execute("SELECT name FROM categories WHERE cat_id = ?", (cat_id,))
        cat_name = cursor.fetchone()[0]
        cursor.execute("SELECT content FROM stock WHERE cat_id = ? AND status = 'available' ORDER BY id ASC", (cat_id,))
        rows = cursor.fetchall()
        conn.close()

        if not rows:
            bot.answer_callback_query(call.id, "এই মুহূর্তে এই ক্যাটাগরিতে কোনো স্টক নেই!", show_alert=True)
            return

        file_content = "\n".join([r[0] for r in rows])
        file_path = f"stock_{cat_id}.txt"
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(file_content)

        with open(file_path, "rb") as f:
            bot.send_document(call.message.chat.id, f, caption=f"{pe('box_package')} <b>{cat_name}</b> এর বর্তমান সমস্ত স্টক ফাইল:", parse_mode="HTML")
        os.remove(file_path)
        return

    elif call.data.startswith("clear_stock_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("clear_stock_", "")
        cursor.execute("UPDATE stock SET status = 'removed' WHERE cat_id = ? AND status = 'available'", (cat_id,))
        conn.commit()
        conn.close()
        bot.answer_callback_query(call.id, "স্টক সফলভাবে মুছে ফেলা হয়েছে!", show_alert=True)

        markup = InlineKeyboardMarkup(row_width=1)
        sub_conn = db_connect()
        sub_cur = sub_conn.cursor()
        sub_cur.execute("SELECT cat_id, name FROM categories WHERE is_active = 1")
        categories = sub_cur.fetchall()
        for cid, name in categories:
            sub_cur.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cid,))
            s_count = sub_cur.fetchone()[0]
            markup.add(premium_inline_button(f"{name} (Stock: {s_count} Pcs)", "manage_stock", callback_data=f"manage_stock_{cid}"))
        sub_conn.close()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))

        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('box_package')} স্টক মুছে ফেলা হয়েছে। অন্য সার্ভিস সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("select_stock_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("select_stock_", "")
        admin_states[user_id] = {"action": "waiting_stock_file", "cat_id": cat_id}
        cursor.execute("SELECT name FROM categories WHERE cat_id = ?", (cat_id,))
        cat_name = cursor.fetchone()[0]
        conn.close()
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data=f"manage_stock_{cat_id}"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('box_package')} আপনি সিলেক্ট করেছেন: <b>{cat_name}</b>\n\nএখন নতুন স্টক ফাইল (.txt) সরাসরি এই চ্যাটে ফাইল হিসেবে আপলোড করে পাঠান।", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_analytics" and user_id == ADMIN_ID:
        cursor.execute("SELECT COUNT(*) FROM users")
        total_users = cursor.fetchone()[0]
        cursor.execute("SELECT SUM(balance) FROM users")
        res_sum = cursor.fetchone()
        total_user_balance = res_sum[0] if res_sum and res_sum[0] is not None else 0.0
        cursor.execute("SELECT user_id, first_name, balance FROM users ORDER BY user_id DESC")
        all_registered = cursor.fetchall()
        conn.close()

        analytics_text = (
            f"{pe('stats_chart')} <b>Live Bot Analytics & Statistics</b>\n\n"
            f"{pe('profile_user')} মোট জয়েনকৃত ইউজার: <b>{total_users} জন</b>\n"
            f"{pe('balance_coin')} ইউজারদের মোট একাউন্ট ব্যালেন্স: <b>৳{total_user_balance}</b>\n\n"
            f"{pe('list_point')} <b>সাম্প্রতিক ইউজার তালিকা:</b>\n"
        )
        for u_id, u_name, u_bal in all_registered[:15]:
            safe_name = u_name or "User"
            analytics_text += f"• {safe_name} (<code>{u_id}</code>) - ৳{u_bal}\n"

        markup = InlineKeyboardMarkup()
        markup.add(
            premium_inline_button("Download Bot Analysis TXT File", "download_txt", callback_data="admin_download_analytics_txt"),
            premium_inline_button("Refresh Live Data", "refresh_data", callback_data="admin_analytics"),
            premium_inline_button("Back", "back_button", callback_data="admin_main")
        )
        try: bot.edit_message_text(analytics_text, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception: pass

    elif call.data == "admin_download_analytics_txt" and user_id == ADMIN_ID:
        cursor.execute("SELECT user_id, first_name FROM users ORDER BY user_id DESC")
        all_users = cursor.fetchall()
        conn.close()

        if not all_users:
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} বোর্ডে কোনো ইউজারের ডাটা পাওয়া যায়নি!", parse_mode="HTML")
            return

        file_content = ""
        for u_id, u_name in all_users:
            safe_name = u_name or "User"
            file_content += f"{u_id} | {safe_name}\n"

        file_path = "bot_analytics_users.txt"
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(file_content)

        with open(file_path, "rb") as f:
            bot.send_document(call.message.chat.id, f, caption=f"{pe('box_package')} Bot Analytics & User List (.txt)\nসকল ইউজারের আইডি দিয়ে তৈরি করা ফাইল:")
        os.remove(file_path)

    elif call.data == "admin_member_balance_list" and user_id == ADMIN_ID:
        cursor.execute("SELECT user_id, first_name, balance FROM users WHERE balance > 0 ORDER BY balance DESC")
        users_with_money = cursor.fetchall()
        conn.close()

        list_text = f"{pe('balance_coin')} <b>যেসব মেম্বারদের অ্যাকাউন্টে টাকা আছে তাদের তালিকা:</b>\n\n"
        if not users_with_money:
            list_text += f"{pe('warn_icon')} এই মুহূর্তে কারও অ্যাকাউন্টে ব্যালেন্স নেই."
        else:
            for idx, (u_id, u_name, u_bal) in enumerate(users_with_money[:20], 1):
                safe_name = u_name or "User"
                list_text += f"{idx}. {safe_name} | ID: <code>{u_id}</code> | ব্যালেন্স: <b>৳{u_bal}</b>\n"

        markup = InlineKeyboardMarkup(row_width=1)
        markup.add(
            premium_inline_button("Download Balance List TXT", "download_txt", callback_data="admin_download_balance_txt"),
            premium_inline_button("Recover Balance List (.txt)", "recover_balance", callback_data="admin_recover_balance_list"),
            premium_inline_button("Back", "back_button", callback_data="admin_main")
        )
        try: bot.edit_message_text(list_text, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=markup)
        except Exception: pass

    elif call.data == "admin_download_balance_txt" and user_id == ADMIN_ID:
        cursor.execute("SELECT user_id, balance, first_name FROM users WHERE balance > 0 ORDER BY balance DESC")
        users_with_money = cursor.fetchall()
        conn.close()

        if not users_with_money:
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} এই মুহূর্তে কারও অ্যাকাউন্টে ব্যালেন্স নেই!", parse_mode="HTML")
            return

        file_content = ""
        for u_id, u_bal, u_name in users_with_money:
            file_content += f"{u_id} | {u_bal}\n"

        file_path = "all_member_balance_list.txt"
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(file_content)

        with open(file_path, "rb") as f:
            bot.send_document(call.message.chat.id, f, caption=f"{pe('box_package')} All Member Balance List (.txt)\nব্যালেন্সধারী মেম্বারদের তালিকা ডাউনলোড হয়েছে:")
        os.remove(file_path)

    elif call.data == "admin_recover_balance_list" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "waiting_recover_balance_txt"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('recover_balance')} <b>Recover Balance List (.txt)</b>\n\nপূর্বে ডাউনলোড করা <code>all_member_balance_list.txt</code> ফাইলটি এখানে আপলোড করুন.", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data == "admin_all_post_edit" and user_id == ADMIN_ID:
        conn.close()
        markup = InlineKeyboardMarkup(row_width=1)
        markup.add(
            premium_inline_button("1. Edit Welcome Post", "post_edit", callback_data="edit_post_welcome_msg"),
            premium_inline_button("2. Edit Channel Not Joined Warning", "post_edit", callback_data="edit_post_not_joined_msg"),
            premium_inline_button("3. Edit Support Text", "post_edit", callback_data="edit_post_support_msg"),
            premium_inline_button("4. Edit Deposit Information Text", "post_edit", callback_data="edit_post_deposit_info_msg"),
            premium_inline_button("Back to Admin", "back_button", callback_data="admin_main")
        )
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('post_edit')} <b>All Post Edit</b>\n\nযেই পোস্টটি এডিট করতে চান সেটির ওপর ক্লিক করুন:", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("edit_post_") and user_id == ADMIN_ID:
        post_key = call.data.replace("edit_post_", "")
        conn.close()
        admin_states[user_id] = {"action": "waiting_generic_post_update", "post_key": post_key}
        current_text = get_setting_msg(post_key, "খালি")
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_all_post_edit"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('post_edit')} <b>Editing Post:</b> <code>{post_key}</code>\n\n<b>বর্তমান লেখা:</b>\n------------------\n{current_text}\n------------------\n\nনতুন লেখাটি পাঠান:", parse_mode="HTML", reply_markup=markup)

    elif call.data == "admin_all_button_edit" and user_id == ADMIN_ID:
        cursor.execute("SELECT cat_id, name FROM categories WHERE is_active = 1")
        categories = cursor.fetchall()
        cursor.execute("SELECT sub_id, sub_name FROM sub_services")
        sub_services = cursor.fetchall()
        conn.close()
        markup = InlineKeyboardMarkup(row_width=1)
        markup.add(InlineKeyboardButton("--- Main Categories ---", callback_data="ignore"))
        for cid, name in categories:
            markup.add(premium_inline_button(name, "edit_pencil", callback_data=f"editbtn_cat_{cid}"))
        if sub_services:
            markup.add(InlineKeyboardButton("--- Sub Packages / VPNs ---", callback_data="ignore"))
            for sid, sname in sub_services:
                markup.add(premium_inline_button(sname, "edit_pencil", callback_data=f"editbtn_sub_{sid}"))
        markup.add(premium_inline_button("Back to Admin", "back_button", callback_data="admin_main"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('button_edit')} <b>All Button Edit</b>\n\nযেই বাটনটি এডিট করতে চান সিলেক্ট করুন:", parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("editbtn_") and user_id == ADMIN_ID:
        parts = call.data.split("_")
        btn_type, btn_id = parts[1], "_".join(parts[2:])
        if btn_type == "cat":
            cursor.execute("SELECT name, price FROM categories WHERE cat_id = ? AND is_active = 1", (btn_id,))
        elif btn_type == "sub":
            cursor.execute("SELECT sub_name, price FROM sub_services WHERE sub_id = ?", (btn_id,))
        else:
            conn.close()
            bot.answer_callback_query(call.id, "এই বাটনটি এডিট করা যাচ্ছে না।", show_alert=True)
            return
        current_button = cursor.fetchone()
        conn.close()
        if not current_button:
            bot.answer_callback_query(call.id, "বাটনটি ডাটাবেজে পাওয়া যায়নি।", show_alert=True)
            return
        admin_states[user_id] = {"action": "waiting_generic_btn_update", "btn_type": btn_type, "btn_id": btn_id}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_all_button_edit"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(
            call.message.chat.id,
            f"{pe('edit_pencil')} এডিট করছেন: <b>{html.escape(str(current_button[0]))}</b> (বর্তমান রেট: ৳{current_button[1]})\n\n"
            f"নতুন নাম ও রেট লিখে পাঠান।\n<b>ফরম্যাট:</b> <code>[নতুন নাম] [নতুন রেট]</code>\n"
            f"<b>উদাহরণ:</b> <code>{html.escape(str(current_button[0]))} {current_button[1]}</code>",
            parse_mode="HTML", reply_markup=markup
        )

    elif call.data == "admin_edit_services" and user_id == ADMIN_ID:
        if user_id in admin_states: del admin_states[user_id]
        cursor.execute("SELECT cat_id, name, price FROM categories WHERE is_active = 1")
        categories = cursor.fetchall()
        conn.close()
        markup = InlineKeyboardMarkup(row_width=1)
        
        markup.add(
            premium_inline_button("Manage Sub-Buttons: Mail Service", "edit_service", callback_data="editsubs_group_mail"),
            premium_inline_button("Manage Sub-Buttons: Proxy Service", "edit_service", callback_data="editsubs_group_proxy"),
            premium_inline_button("Manage Sub-Buttons: Telegram Premium Buy", "edit_service", callback_data="editsubs_telegram_premium"),
            premium_inline_button("Manage Sub-Buttons: VPN Service", "edit_service", callback_data="editsubs_vpn_service")
        )
        
        special_ids = ["telegram_premium", "vpn_service"]
        regular_cats = [c for c in categories if c[0] not in special_ids and c[0] not in ['hotmail', 'outlook', 'Outlook fr', 'Ig Hotmail', 'proxy']]
        
        for cat_id, name, price in regular_cats:
            sub_conn = db_connect()
            sub_cursor = sub_conn.cursor()
            sub_cursor.execute("SELECT COUNT(*) FROM stock WHERE cat_id = ? AND status = 'available'", (cat_id,))
            stock_count = sub_cursor.fetchone()[0]
            sub_conn.close()
            markup.add(
                premium_inline_button(f"{name} | ৳{price} | Stock: {stock_count}", "edit_service", callback_data=f"editcat_{cat_id}"),
                premium_inline_button(f"Delete {name}", "delete_trash", callback_data=f"confirm_del_{cat_id}")
            )
        
        markup.add(
            premium_inline_button("Add New Button / Service", "add_balance", callback_data="admin_add_new_btn"),
            premium_inline_button("Back", "back_button", callback_data="admin_main")
        )
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('edit_service')} সার্ভিস এডিট বা ডিলিট করতে নিচের বাটনগুলোতে ক্লিক করুন:", parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("confirm_del_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("confirm_del_", "")
        cursor.execute("SELECT name FROM categories WHERE cat_id = ?", (cat_id,))
        cat_res = cursor.fetchone()
        cat_name = cat_res[0] if cat_res else "এই সার্ভিসটি"
        conn.close()

        markup = InlineKeyboardMarkup(row_width=2)
        markup.add(
            premium_inline_button("Yes (Delete)", "approve_btn", callback_data=f"delcat_{cat_id}"),
            premium_inline_button("No (Cancel)", "reject_btn", callback_data="admin_edit_services")
        )
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('warn_icon')} <b>সতর্কবার্তা!</b>\n\nআপনি কি সত্যি <b>{cat_name}</b> বাটনটি ডিলিট করতে চাচ্ছেন?", parse_mode="HTML", reply_markup=markup)
        return

    elif call.data.startswith("editsubs_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("editsubs_", "")
        if cat_id == "vpn_service":
            conn.close()
            markup = InlineKeyboardMarkup(row_width=2)
            markup.add(
                premium_inline_button("Manage 3 Day", "edit_service", callback_data="editsubs_vpn_3d"),
                premium_inline_button("Manage 7 Day", "edit_service", callback_data="editsubs_vpn_7d"),
                premium_inline_button("Manage 14 Day", "edit_service", callback_data="editsubs_vpn_14d"),
                premium_inline_button("Manage 30 Day", "edit_service", callback_data="editsubs_vpn_30d"),
                premium_inline_button("Back", "back_button", callback_data="admin_edit_services")
            )
            try: bot.delete_message(call.message.chat.id, call.message.message_id)
            except Exception: pass
            bot.send_message(call.message.chat.id, f"{pe('edit_service')} <b>VPN Service Sub-Packages Manage:</b>\nমেয়াদ অনুযায়ী প্যাকেজ ম্যানেজ করুন:", parse_mode="HTML", reply_markup=markup)
            return

        if cat_id in ("group_mail", "group_proxy"):
            g_type = 'mail' if cat_id == "group_mail" else 'proxy'
            cursor.execute("SELECT cat_id, name, price FROM categories WHERE group_type = ? AND is_active = 1", (g_type,))
            items = cursor.fetchall()
            conn.close()

            markup = InlineKeyboardMarkup(row_width=1)
            for c_id, c_name, c_price in items:
                markup.add(
                    premium_inline_button(f"Edit: {c_name} (৳{c_price})", "edit_service", callback_data=f"editcat_{c_id}"),
                    premium_inline_button(f"Delete: {c_name}", "delete_trash", callback_data=f"confirm_del_{c_id}")
                )
            
            markup.add(
                premium_inline_button("Add New Service / Button", "add_balance", callback_data="admin_add_new_btn"),
                premium_inline_button("Back", "back_button", callback_data="admin_edit_services")
            )
            try: bot.delete_message(call.message.chat.id, call.message.message_id)
            except Exception: pass
            bot.send_message(call.message.chat.id, f"{pe('edit_service')} <b>Manage {('Mail Service' if g_type=='mail' else 'Proxy Service')}:</b>", parse_mode="HTML", reply_markup=markup)
            return

        cursor.execute("SELECT sub_id, sub_name, price FROM sub_services WHERE cat_id = ?", (cat_id,))
        subs = cursor.fetchall()
        conn.close()

        markup = InlineKeyboardMarkup(row_width=1)
        for sub_id, sub_name, price in subs:
            markup.add(
                premium_inline_button(f"Edit: {sub_name} (৳{price})", "edit_service", callback_data=f"editsubitem_{sub_id}_{cat_id}"),
                premium_inline_button(f"Delete: {sub_name}", "delete_trash", callback_data=f"delsub_{sub_id}_{cat_id}")
            )
        
        markup.add(
            premium_inline_button("Add New Package", "add_balance", callback_data=f"addsub_{cat_id}"),
            premium_inline_button("Back", "back_button", callback_data="admin_edit_services")
        )
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('edit_service')} <b>Manage Sub-Buttons:</b>", parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("editsubitem_") and user_id == ADMIN_ID:
        parts = call.data.split("_")
        sub_id, cat_id = parts[1], parts[2]
        cursor.execute("SELECT sub_name, price FROM sub_services WHERE sub_id = ?", (sub_id,))
        sub_item = cursor.fetchone()
        conn.close()
        admin_states[user_id] = {"action": "waiting_generic_btn_update", "btn_type": "sub", "btn_id": sub_id}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data=f"editsubs_{cat_id}"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('edit_pencil')} এডিট করছেন: <b>{sub_item[0]}</b> (মূল্য: ৳{sub_item[1]})\n\nনতুন নাম ও রেট লিখে পাঠান:\n<b>ফরম্যাট:</b> <code>[নাম] [রেট]</code>", parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("delsub_") and user_id == ADMIN_ID:
        parts = call.data.split("_")
        sub_id, cat_id = parts[1], parts[2]
        cursor.execute("DELETE FROM sub_services WHERE sub_id = ?", (sub_id,))
        conn.commit()
        conn.close()
        bot.answer_callback_query(call.id, "প্যাকেজ ডিলিট হয়েছে!")
        return

    elif call.data.startswith("addsub_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("addsub_", "")
        conn.close()
        admin_states[user_id] = {"action": "adding_sub_item", "cat_id": cat_id}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data=f"editsubs_{cat_id}"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('add_balance')} নতুন প্যাকেজের নাম এবং দাম লিখে পাঠান:\n<code>[Package Name] [Price]</code>", parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("editcat_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("editcat_", "")
        cursor.execute("SELECT name, price FROM categories WHERE cat_id = ?", (cat_id,))
        cat = cursor.fetchone()
        conn.close()
        admin_states[user_id] = {"action": "waiting_generic_btn_update", "btn_type": "cat", "btn_id": cat_id}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_edit_services"))
        edit_prompt = f"{pe('edit_pencil')} এডিট করছেন: <b>{cat[0]}</b> (বর্তমান মূল্য: ৳{cat[1]})\n\nনতুন নাম এবং রেট লিখে পাঠান.\n<b>ফরম্যাট:</b> <code>[নতুন নাম] [রেট]</code>"
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, edit_prompt, parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("delcat_") and user_id == ADMIN_ID:
        cat_id = call.data.replace("delcat_", "")
        cursor.execute("UPDATE categories SET is_active = 0 WHERE cat_id = ?", (cat_id,))
        cursor.execute("UPDATE stock SET status = 'removed' WHERE cat_id = ? AND status = 'available'", (cat_id,))
        cursor.execute("DELETE FROM sub_services WHERE cat_id = ?", (cat_id,))
        conn.commit()
        conn.close()
        bot.send_message(call.message.chat.id, f"{pe('step_tick')} সার্ভিসটি সফলভাবে ডিলিট করা হয়েছে!", parse_mode="HTML")

    elif call.data == "admin_add_new_btn" and user_id == ADMIN_ID:
        conn.close()
        admin_states[user_id] = {"action": "adding_new_cat"}
        markup = InlineKeyboardMarkup()
        markup.add(premium_inline_button("Back", "back_button", callback_data="admin_edit_services"))
        try: bot.delete_message(call.message.chat.id, call.message.message_id)
        except Exception: pass
        bot.send_message(call.message.chat.id, f"{pe('add_balance')} নতুন বাটন যোগ করতে ফরম্যাটে নাম এবং দাম লিখে পাঠান:\n<code>[Button Name] [Price]</code>", parse_mode="HTML", reply_markup=markup)

    elif call.data.startswith("app_") and user_id == ADMIN_ID:
        req_id = call.data.split("_")[1]
        if req_id in pending_deposits:
            data = pending_deposits[req_id]
            target_user, amount, method = data["user_id"], data["amount"], data.get("method", "Payment")
            
            cursor.execute("SELECT user_id, referred_by FROM users WHERE user_id = ?", (target_user,))
            user_row = cursor.fetchone()
            
            if not user_row:
                cursor.execute("INSERT INTO users (user_id, first_name, balance, username, referred_by) VALUES (?, ?, ?, 'N/A', NULL)", (target_user, "User", amount))
                referred_by = None
            else:
                cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (amount, target_user))
                referred_by = user_row[1]
            conn.commit()
            
            if referred_by:
                referral_bonus_amount = 0.02
                cursor.execute("SELECT user_id FROM users WHERE user_id = ?", (referred_by,))
                referrer_exists = cursor.fetchone()
                if referrer_exists:
                    credited_at = datetime.now(timezone.utc).isoformat()
                    cursor.execute(
                        "INSERT OR IGNORE INTO referral_deposit_bonus_ledger (deposit_request_id, referrer_id, referred_user_id, deposit_amount, bonus_amount, credited_at) VALUES (?, ?, ?, ?, ?, ?)",
                        (req_id, referred_by, target_user, amount, referral_bonus_amount, credited_at)
                    )
                    if cursor.rowcount > 0:
                        cursor.execute(
                            "UPDATE users SET balance = balance + ?, referral_deposit_bonus = COALESCE(referral_deposit_bonus, 0) + ? WHERE user_id = ?",
                            (referral_bonus_amount, referral_bonus_amount, referred_by)
                        )
                        conn.commit()
                        try:
                            bot.send_message(
                                referred_by,
                                f"<tg-emoji emoji-id=\"6131890186767831988\">🎁</tg-emoji> <b>রেফারেল ডিপোজিট বোনাস!</b>\nআপনার রেফারেল থেকে একজন মেম্বার সফলভাবে ডিপোজিট করেছেন। আপনার মেইন ব্যালেন্সে <b>0.02 টাকা</b> যোগ হয়েছে এবং Referral Deposit Bonus-এ স্থায়ীভাবে জমা হয়েছে।",
                                parse_mode="HTML"
                            )
                        except Exception:
                            pass

            conn.close()
            bot.send_message(target_user, f"{pe('deposit_success')} <b>আপনার ডিপোজিট সফল হয়েছে!</b>\nআপনার একাউন্টে ৳<b>{amount}</b> যোগ করা হয়েছে। এখন আপনি কেনাকাটা করতে পারেন।", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_user))
            try:
                bot.edit_message_caption(f"✅ Approved Successfully (User ID: {target_user}, Amount: ৳{amount}, Method: {method})", call.message.chat.id, call.message.message_id, reply_markup=None)
            except Exception:
                try:
                    bot.edit_message_text(f"✅ Approved Successfully (User ID: {target_user}, Amount: ৳{amount}, Method: {method})", call.message.chat.id, call.message.message_id, reply_markup=None)
                except Exception:
                    pass
            del pending_deposits[req_id]
        else:
            conn.close()
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} এই রিকোয়েস্টটি ইতিমধ্যে প্রসেস করা হয়েছে!", parse_mode="HTML")

    elif call.data.startswith("rej_") and user_id == ADMIN_ID:
        req_id = call.data.split("_")[1]
        if req_id in pending_deposits:
            data = pending_deposits[req_id]
            target_user = data["user_id"]
            conn.close()
            bot.send_message(target_user, f"{pe('warn_icon')} আপনি ভুল তথ্য বা স্ক্রিনশট দিয়েছেন, তাই আপনার অর্ডারটি রিজেক্ট করা হলো। সঠিক তথ্য দিয়ে পুনরায় চেষ্টা করুন।", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_user))
            try:
                bot.edit_message_caption(f"❌ Rejected (User ID: {target_user})", call.message.chat.id, call.message.message_id)
            except Exception:
                bot.send_message(call.message.chat.id, f"❌ Rejected (User ID: {target_user})")
            del pending_deposits[req_id]
        else:
            conn.close()
            bot.send_message(call.message.chat.id, f"{pe('warn_icon')} এই রিকোয়েস্টটি ইতিমধ্যে প্রসেস করা হয়েছে!", parse_mode="HTML")

    elif call.data.startswith("complete_order_") and user_id == ADMIN_ID:
        target_user = int(call.data.split("_")[2])
        conn.close()
        admin_states[user_id] = {"action": "waiting_delivery_content", "target_user": target_user}
        bot.send_message(call.message.chat.id, f"{pe('list_point')} ইউজার ID: <code>{target_user}</code> এর অর্ডারের জন্য মেসেজ বা ডাটা লিখে পাঠান:", parse_mode="HTML")

    elif call.data.startswith("vpn_nostock_cancel_") and user_id == ADMIN_ID:
        parts = call.data.split("_")
        target_user = int(parts[3])
        refund_amount = float(parts[4])
        
        cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (refund_amount, target_user))
        conn.commit()
        conn.close()

        try:
            bot.send_message(
                target_user,
                f"{pe('no_stock')} <b>দুঃখিত, আপনার অর্ডারটি ক্যানসেল করা হয়েছে!</b>\n\n"
                f"আপনি যে ভিপিএন প্রোডাক্টটি অর্ডার করেছিলেন সেটি বর্তমানে আমাদের স্টকে নেই। "
                f"তাই আপনার অর্ডারটি ক্যানসেল করে আপনার পরিশোধিত ৳<b>{refund_amount}</b> টাকা আপনার অ্যাকাউন্টে ব্যাক (রিফান্ড) করে দেওয়া হয়েছে।",
                parse_mode="HTML",
                reply_markup=get_permanent_keyboard(target_user)
            )
        except Exception:
            pass

        bot.answer_callback_query(call.id, "অর্ডার সফলভাবে ক্যানসেল করা হয়েছে এবং ইউজারের টাকা রিফান্ড করা হয়েছে!", show_alert=True)
        try:
            bot.edit_message_caption(f"❌ VPN Order Cancelled & Refunded (User ID: {target_user}, Refund: ৳{refund_amount})", call.message.chat.id, call.message.message_id)
        except Exception:
            pass
        return

    else:
        conn.close()

@bot.message_handler(content_types=['document'])
def handle_stock_file(message):
    update_owner_premium_status(message.from_user)
    user_id = message.from_user.id
    save_user_id_to_file(user_id)
    
    if user_id in user_temp_deposit and user_temp_deposit[user_id].get("step") == "waiting_screenshot":
        file_id = message.document.file_id
        process_deposit_submission(message, file_id, is_document=True)
        return

    if user_id == ADMIN_ID and user_id in admin_states:
        action = admin_states[user_id].get("action")

        if action == "waiting_premium_emoji_txt":
            try:
                file_info = bot.get_file(message.document.file_id)
                downloaded_file = bot.download_file(file_info.file_path)
                file_content = downloaded_file.decode('utf-8', errors='ignore')
                mapping, legacy_entries = parse_premium_emoji_mapping(file_content)
                if legacy_entries:
                    conn = db_connect()
                    cur = conn.cursor()
                    for legacy_key, legacy_id in legacy_entries.items():
                        cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (PREMIUM_EMOJI_PREFIX + legacy_key, legacy_id))
                    conn.commit()
                    conn.close()
                if not mapping:
                    bot.reply_to(message, f"{pe('warn_icon')} কোনো valid emoji পাওয়া যায়নি।", parse_mode="HTML")
                    return
                save_premium_emoji_mapping(mapping)
                del admin_states[user_id]
                bot.reply_to(message, f"{pe('step_tick')} <b>Premium Emoji Set সফলভাবে save হয়েছে!</b>", parse_mode="HTML")
            except Exception as e:
                bot.reply_to(message, f"{pe('warn_icon')} ত্রুটি ঘটেছে: {e}")
            return

        if action == "waiting_stock_file":
            cat_id = admin_states[user_id]["cat_id"]
            try:
                file_info = bot.get_file(message.document.file_id)
                downloaded_file = bot.download_file(file_info.file_path)
                file_content = downloaded_file.decode('utf-8', errors='ignore')
                lines = [line.strip() for line in file_content.splitlines() if line.strip()]
                
                if not lines:
                    bot.reply_to(message, f"{pe('warn_icon')} ফাইলটি খালি রয়েছে।", parse_mode="HTML")
                    return
                
                conn = db_connect()
                cursor = conn.cursor()
                added_count = 0
                for line in lines:
                    cursor.execute("INSERT INTO stock (cat_id, content) VALUES (?, ?)", (cat_id, line))
                    added_count += 1
                conn.commit()
                
                cursor.execute("SELECT user_id FROM users")
                all_users = cursor.fetchall()
                cursor.execute("SELECT name FROM categories WHERE cat_id = ?", (cat_id,))
                cat_row = cursor.fetchone()
                cat_name = cat_row[0] if cat_row else cat_id
                conn.close()
                
                broadcast_text = (
                    f"{pe('alarm_bell')} <b>নতুন স্টক আপডেট!</b>\n\n"
                    f"আমাদের বটে নতুন স্টক যুক্ত হয়েছে: <b>{cat_name}</b>\n"
                    f"এখনই আপনার অ্যাকাউন্ট থেকে পর্যাপ্ত ব্যালেন্স দিয়ে খুব সহজে কিনে নিন। স্টক সীমিত!"
                )
                for u in all_users:
                    try: bot.send_message(u[0], broadcast_text, parse_mode="HTML", reply_markup=get_permanent_keyboard(u[0]))
                    except Exception: pass

                del admin_states[user_id]
                bot.reply_to(message, f"{pe('step_tick')} সফলভাবে মোট <b>{added_count}টি</b> স্টক যোগ করা হয়েছে এবং মেম্বারদের নোটিফিকেশন পাঠানো হয়েছে!", parse_mode="HTML")
            except Exception as e:
                bot.reply_to(message, f"ফাইল প্রসেস করতে সমস্যা হয়েছে: {e}")
            return

        elif action == "waiting_recover_balance_txt":
            try:
                file_info = bot.get_file(message.document.file_id)
                downloaded_file = bot.download_file(file_info.file_path)
                file_content = downloaded_file.decode('utf-8', errors='ignore')
                lines = [line.strip() for line in file_content.splitlines() if line.strip()]
                
                conn = db_connect()
                cursor = conn.cursor()
                recovered_count = 0
                for line in lines:
                    numbers = re.findall(r'\d+(?:\.\d+)?', line)
                    if len(numbers) >= 2:
                        try:
                            target_uid, balance_amount = int(numbers[0]), float(numbers[1])
                            cursor.execute("SELECT user_id FROM users WHERE user_id = ?", (target_uid,))
                            if not cursor.fetchone():
                                cursor.execute("INSERT INTO users (user_id, first_name, balance, username) VALUES (?, ?, ?, 'N/A')", (target_uid, "User", balance_amount))
                            else:
                                cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (balance_amount, target_uid))
                            conn.commit()
                            recovered_count += 1
                            try:
                                bot.send_message(target_uid, f"{pe('deposit_success')} <b>ব্যালেন্স রিকভারি আপডেট!</b>\n\nআপনার একাউন্টে পূর্বের <b>৳{balance_amount}</b> জমা দেওয়া হয়েছে!", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_uid))
                            except Exception: pass
                        except ValueError: pass
                
                conn.close()
                del admin_states[user_id]
                bot.reply_to(message, f"{pe('step_tick')} রিকভারি সম্পূর্ণ হয়েছে! মোট <b>{recovered_count} জন</b> ইউজারের ব্যালেন্স সফলভাবে ব্যাক করা হয়েছে।", parse_mode="HTML")
            except Exception as e:
                bot.reply_to(message, f"ফাইল পড়তে ত্রুটি ঘটেছে: {e}")
            return

        elif action == "waiting_analysis_txt_for_broadcast":
            try:
                file_info = bot.get_file(message.document.file_id)
                downloaded_file = bot.download_file(file_info.file_path)
                file_content = downloaded_file.decode('utf-8', errors='ignore')
                
                found_ids = re.findall(r'\b\d{6,12}\b', file_content)
                target_user_ids = list(set([int(uid) for uid in found_ids]))

                if not target_user_ids:
                    bot.reply_to(message, f"{pe('warn_icon')} ফাইল থেকে কোনো ইউজারের সঠিক আইডি খুঁজে পাওয়া যায়নি।", parse_mode="HTML")
                    return

                admin_states[user_id] = {
                    "action": "waiting_live_broadcast_message",
                    "target_uids": target_user_ids
                }

                bot.reply_to(
                    message,
                    f"{pe('step_tick')} ফাইল ডিটেকশন সফল হয়েছে! মোট <b>{len(target_user_ids)} জন</b> ইউজার পাওয়া গেছে।\n\n"
                    f"{pe('list_point')} <b>আপনি সবার উদ্দেশ্যে কি পাঠাতে চান?</b>\n"
                    f"(টেক্সট, ছবি, ভয়েস মেসেজ, ভিডিও বা ফাইল সরাসরি পাঠিয়ে দিন):",
                    parse_mode="HTML"
                )
            except Exception as e:
                bot.reply_to(message, f"ফাইল পড়তে সমস্যা হয়েছে: {e}")
            return

def process_deposit_submission(message, file_id, is_document=False):
    update_owner_premium_status(message.from_user)
    user_id = message.from_user.id
    raw_first_name = message.from_user.first_name or "N/A"
    raw_username = f"@{message.from_user.username}" if message.from_user.username else "N/A"
    
    first_name = html.escape(raw_first_name)
    username = html.escape(raw_username)
    
    save_user_id_to_file(user_id)

    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("UPDATE users SET username = ? WHERE user_id = ?", (raw_username, user_id))
    conn.commit()
    conn.close()

    if user_id in user_temp_deposit and user_temp_deposit[user_id].get("step") == "waiting_screenshot":
        data = user_temp_deposit[user_id]
        amount = data.get("amount", 0.0)
        raw_trx = str(data.get("trx_id", "N/A"))
        trx_id = html.escape(raw_trx)
        method = html.escape(str(data.get("method", "Payment")))

        bot.reply_to(
            message,
            f"{pe('waiting_clock')} <b>প্রিয় কাস্টমার দয়া করে ২ - ৩ মিনিট অপেক্ষা করুন, অ্যাকাউন্টে টাকা যোগ হচ্ছে...</b>",
            parse_mode="HTML",
            reply_markup=get_permanent_keyboard(user_id)
        )

        req_id = str(uuid.uuid4())[:8]
        pending_deposits[req_id] = {
            "user_id": user_id,
            "amount": amount,
            "trx_id": raw_trx,
            "method": method
        }
        del user_temp_deposit[user_id]

        admin_markup = InlineKeyboardMarkup()
        admin_markup.add(
            premium_inline_button("Approve", "approve_btn", callback_data=f"app_{req_id}"),
            premium_inline_button("Reject", "reject_btn", callback_data=f"rej_{req_id}")
        )

        caption_text = (
            f"{pe('alarm_bell')} <b>New Payment Request Received!</b>\n\n"
            f"{pe('profile_user')} <b>Name:</b> <b>{first_name}</b>\n"
            f"{pe('username_link')} <b>Username:</b> <b>{username}</b>\n"
            f"{pe('id_badge')} <b>User ID:</b> <code>{user_id}</code>\n"
            f"{pe('deposit_money')} <b>Amount:</b> <b>৳{amount}</b>\n"
            f"{pe('sendmoney_shield')} <b>Payment Method:</b> <b>{method}</b>\n"
            f"{pe('trx_input')} <b>TrxID:</b> <code>{trx_id}</code>\n\n"
            f"Please verify payment and take action below:"
        )

        target_notify_chat = ADMIN_ID
        deposit_group = get_setting_msg('deposit_group_id', '')
        if deposit_group:
            try:
                target_notify_chat = int(deposit_group)
            except ValueError:
                target_notify_chat = deposit_group

        for i in range(3):
            try:
                bot.send_message(
                    target_notify_chat, 
                    f"{pe('alarm_bell')} <b>[ALARM {i+1}/3] নতুন ডিপোজিট ও পেমেন্ট এসেছে! দ্রুত এপ্রুভ করুন। টং টং! 🛎️🔔</b>", 
                    parse_mode="HTML"
                )
                time.sleep(0.3)
            except Exception:
                pass

        try:
            if not is_document:
                bot.send_photo(target_notify_chat, file_id, caption=caption_text, parse_mode="HTML", reply_markup=admin_markup)
            else:
                bot.send_document(target_notify_chat, file_id, caption=caption_text, parse_mode="HTML", reply_markup=admin_markup)
        except Exception as e:
            bot.send_message(ADMIN_ID, caption_text, parse_mode="HTML", reply_markup=admin_markup)

@bot.message_handler(content_types=['text', 'photo', 'voice', 'audio', 'video', 'document'])
def handle_all_messages_and_broadcast(message):
    update_owner_premium_status(message.from_user)
    user_id = message.from_user.id
    username = f"@{message.from_user.username}" if message.from_user.username else "N/A"
    save_user_id_to_file(user_id)

    conn = db_connect()
    cursor = conn.cursor()
    cursor.execute("UPDATE users SET username = ? WHERE user_id = ?", (username, user_id))
    conn.commit()
    conn.close()

    text = message.text if message.text else ""

    if user_id == ADMIN_ID and _gw_admin_text(message, user_id, text):
        return

    # Independent Telegram Member Sell link/order flow.
    if user_id in member_sell_states:
        state_data = member_sell_states[user_id]
        if state_data.get("step") == "waiting_target_link":
            target_link = (text or "").strip()
            if target_link.lower() == "cancel":
                del member_sell_states[user_id]
                bot.send_message(
                    user_id,
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} অর্ডার প্রক্রিয়া বাতিল করা হয়েছে। কোনো টাকা কাটা হয়নি।",
                    parse_mode="HTML",
                    reply_markup=get_permanent_keyboard(user_id)
                )
                return
            if message.content_type != "text" or not is_valid_member_sell_target(target_link):
                bot.send_message(
                    user_id,
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_target'])} সঠিক Telegram Username অথবা Link দিন। উদাহরণ: <code>@channelname</code> অথবা <code>https://t.me/channelname</code>",
                    parse_mode="HTML"
                )
                return

            conn = db_connect()
            cur = conn.cursor()
            try:
                cur.execute("BEGIN IMMEDIATE")
                cur.execute("SELECT balance, first_name, username FROM users WHERE user_id = ? FOR UPDATE", (user_id,))
                user_row = cur.fetchone()
                if not user_row:
                    conn.rollback()
                    conn.close()
                    bot.send_message(user_id, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} আপনার অ্যাকাউন্ট পাওয়া যায়নি। /start দিয়ে আবার চেষ্টা করুন।", parse_mode="HTML")
                    del member_sell_states[user_id]
                    return
                current_balance, first_name, saved_username = user_row
                price = float(state_data["price"])
                if float(current_balance or 0) < price:
                    conn.rollback()
                    conn.close()
                    bot.send_message(
                        user_id,
                        f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_price'])} আপনার পর্যাপ্ত ব্যালেন্স নেই।\nপ্যাকেজ মূল্য: ৳{price:g}\n{member_sell_emoji(MEMBER_SELL_EMOJIS['success_balance'])} আপনার ব্যালেন্স: ৳{float(current_balance or 0):g}",
                        parse_mode="HTML",
                        reply_markup=get_permanent_keyboard(user_id)
                    )
                    del member_sell_states[user_id]
                    return

                new_balance = float(current_balance or 0) - price
                order_id = uuid.uuid4().hex
                created_at = datetime.now(timezone.utc).isoformat()
                cur.execute("UPDATE users SET balance = ? WHERE user_id = ?", (new_balance, user_id))
                cur.execute(
                    "INSERT INTO member_sell_orders (order_id, user_id, first_name, username, duration_key, duration_label, quantity, price, target_link, status, created_at) "
                    "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 'pending', ?)",
                    (order_id, user_id, first_name or message.from_user.first_name or "User", username if username != "N/A" else (saved_username or "N/A"),
                     state_data["duration_key"], state_data["duration_label"], state_data["quantity"], price, target_link, created_at)
                )
                conn.commit()
            except Exception as e:
                conn.rollback()
                conn.close()
                print(f"Telegram Member Sell order create error: {e}")
                bot.send_message(user_id, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} অর্ডারটি তৈরি করা যায়নি। কোনো টাকা কাটা হয়নি। আবার চেষ্টা করুন।", parse_mode="HTML")
                return
            conn.close()
            del member_sell_states[user_id]

            quantity = int(state_data["quantity"])
            duration_label = state_data["duration_label"]
            qty_label = f"{quantity // 1000}k" if quantity >= 1000 else str(quantity)
            safe_name = html.escape(first_name or message.from_user.first_name or "User")
            safe_username = html.escape(username)
            safe_link = html.escape(target_link)

            try:
                bot.send_message(
                    user_id,
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>আপনার Telegram Member Sell অর্ডারটি সফলভাবে সাবমিট হয়েছে!</b>\n\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['duration'])} <b>মেয়াদ:</b> {html.escape(duration_label)}\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>মেম্বার:</b> {qty_label} জন\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_price'])} <b>মূল্য:</b> ৳{price:g}\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['success_balance'])} <b>অবশিষ্ট ব্যালেন্স:</b> ৳{new_balance:g}\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['success_order_id'])} <b>Order ID:</b> <code>{order_id}</code>\n\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['delivery'])} অর্ডারটি কিছুক্ষণের মধ্যে আপনার চ্যানেল বা গ্রুপে রানিং হয়ে যাবে। কিছুক্ষণ অপেক্ষা করুন।",
                    parse_mode="HTML",
                    reply_markup=get_permanent_keyboard(user_id)
                )
            except Exception as e:
                print(f"Telegram Member Sell buyer notification failed: {e}")

            admin_markup = InlineKeyboardMarkup(row_width=1)
            admin_markup.add(
                premium_inline_button("Service Complete", "6269285159774720688", callback_data=f"ms_complete_{order_id}"),
                premium_inline_button("No Delivery", "6068810023566317366", callback_data=f"ms_refund_{order_id}")
            )
            admin_order_msg = (
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>New Telegram Member Sell Order</b>\n\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['success_order_id'])} <b>Order ID:</b> <code>{order_id}</code>\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['admin_name'])} <b>Name:</b> {safe_name}\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['admin_username'])} <b>Telegram Username:</b> {safe_username}\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['admin_user_id'])} <b>User ID:</b> <code>{user_id}</code>\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>Service:</b> Telegram Member Sell\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['duration'])} <b>Duration:</b> {html.escape(duration_label)}\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>Members:</b> {qty_label}\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['prompt_price'])} <b>Price:</b> ৳{price:g}\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['admin_link'])} <b>Channel/Group Link:</b> {safe_link}\n"
                f"{member_sell_emoji(MEMBER_SELL_EMOJIS['admin_status'])} <b>Order Status:</b> Pending"
            )
            try:
                bot.send_message(ADMIN_ID, admin_order_msg, parse_mode="HTML", reply_markup=admin_markup)
            except Exception as e:
                print(f"Telegram Member Sell admin notification failed: {e}")
                try:
                    bot.send_message(user_id, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} অর্ডারটি সেভ হয়েছে, তবে অ্যাডমিনকে নোটিফিকেশন পাঠানো যায়নি। সাপোর্টে যোগাযোগ করুন।", parse_mode="HTML")
                except Exception:
                    pass
            return

    if user_id in user_temp_deposit:
        state = user_temp_deposit[user_id].get("step")

        if state == "waiting_amount":
            try:
                amount = float(text)
                if amount < 10 or amount > 10000:
                    bot.send_message(user_id, f"{pe('warn_icon')} সর্বনিম্ন ১০ টাকা এবং সর্বোচ্চ ১০,০০০ টাকা ডিপোজিট করতে পারবেন। সঠিক পরিমাণ দিন:", parse_mode="HTML")
                    return
                user_temp_deposit[user_id]["amount"] = amount
                user_temp_deposit[user_id]["step"] = "waiting_method"
                bot.send_message(user_id, f"{pe('sendmoney_shield')} <b>আপনি কিসের মাধ্যমে পেমেন্ট করতে চাচ্ছেন সিলেক্ট করুন:</b>", parse_mode="HTML", reply_markup=get_payment_method_markup())
                return
            except ValueError:
                bot.send_message(user_id, f"{pe('warn_icon')} দয়া করে সঠিক সংখ্যা লিখুন (যেমন: 50 বা 500)।", parse_mode="HTML", reply_markup=get_permanent_keyboard(user_id))
                return

        elif state == "waiting_trx" and not (user_temp_deposit[user_id].get("method") == "Binance" and not pgw.binance_history_configured()):
            # bKash / Nagad / Rocket / Binance (verified automatically): no screenshot needed.
            _gw_submit_trx(message, user_id, text)
            return

        elif state == "waiting_trx":
            # Binance without API keys configured: original manual screenshot flow is kept.
            user_temp_deposit[user_id]["trx_id"] = text.strip()
            user_temp_deposit[user_id]["step"] = "waiting_screenshot"
            bot.send_message(
                user_id,
                f"{pe('step_tick')} <b>ধন্যবাদ! আপনার ট্রানজেকশন আইডি গ্রহণ করা হয়েছে।</b>\n\n"
                f"{pe('camera_icon')} এখন পেমেন্টের একটি স্ক্রিনশট (Screenshot) এই চ্যাটে পাঠান:",
                parse_mode="HTML",
                reply_markup=get_permanent_keyboard(user_id)
            )
            return

        elif state == "waiting_service_username":
            data = user_temp_deposit[user_id]
            cat_id, sub_name, price, username_input = data["cat_id"], data["sub_name"], data["price"], text.strip()
            del user_temp_deposit[user_id]

            conn = db_connect()
            cursor = conn.cursor()
            cursor.execute("SELECT balance FROM users WHERE user_id = ? FOR UPDATE", (user_id,))
            bal_res = cursor.fetchone()
            current_bal = bal_res[0] if bal_res else 0.0

            if current_bal < price:
                conn.close()
                bot.send_message(user_id, f"{pe('insufficient_bal')} আপনার একাউন্টে পর্যাপ্ত ব্যালেন্স নেই!", parse_mode="HTML", reply_markup=get_permanent_keyboard(user_id))
                return

            new_bal = current_bal - price
            cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (new_bal, user_id))
            conn.commit()
            conn.close()

            is_vpn_order = "vpn_" in cat_id or "Day" in sub_name
            emoji_k = "telegram_premium_cat" if "telegram" in cat_id else get_vpn_emoji_key(sub_name)
            
            bot.send_message(
                user_id,
                f"{pe('order_pending')} আপনার অর্ডারটি সফলভাবে সাবমিট হয়েছে!\n\n"
                f"{pe(emoji_k)} সার্ভিস: <b>{sub_name}</b> {pe(emoji_k)}\n"
                f"{pe('profile_user')} ইউজারনেম/আইডি: <code>{username_input}</code>\n"
                f"{pe('money_spent')} পরিশোধিত মূল্য: ৳{price}\n"
                f"{pe('wallet_balance')} অবশিষ্ট ব্যালেন্স: ৳{new_bal}\n\n"
                f"{pe('waiting_clock')} দয়া করে কিছুক্ষণ অপেক্ষা করুন, অ্যাডমিন খুব শীঘ্রই আপনার সার্ভিসটি কমপ্লিট করে দেবেন।",
                parse_mode="HTML",
                reply_markup=get_permanent_keyboard(user_id)
            )

            admin_markup = InlineKeyboardMarkup(row_width=1)
            admin_markup.add(
                premium_inline_button("Complete Order & Deliver", "approve_btn", callback_data=f"complete_order_{user_id}"),
            )
            if is_vpn_order:
                admin_markup.add(
                    premium_inline_button("No Stock Cancel Delivery", "reject_btn", callback_data=f"vpn_nostock_cancel_{user_id}_{price}")
                )

            admin_order_msg = (
                f"{pe('alarm_bell')} <b>New VPN / Service Order Received!</b>\n\n"
                f"{pe('profile_user')} <b>User ID:</b> <code>{user_id}</code>\n"
                f"{pe('box_package')} <b>Service:</b> <b>{sub_name}</b>\n"
                f"{pe('username_link')} <b>Target Account:</b> <code>{username_input}</code>\n"
                f"{pe('money_spent')} <b>Price:</b> ৳{price}"
            )

            for i in range(3):
                try:
                    bot.send_message(
                        ADMIN_ID, 
                        f"{pe('alarm_bell')} <b>[ORDER ALARM {i+1}/3] নতুন ভিপিএন অর্ডার এসেছে! টং টং! 🛎️🔔</b>", 
                        parse_mode="HTML"
                    )
                    time.sleep(0.3)
                except Exception:
                    pass

            bot.send_message(ADMIN_ID, admin_order_msg, parse_mode="HTML", reply_markup=admin_markup)
            return

    if user_id == ADMIN_ID and user_id in admin_states:
        state_data = admin_states[user_id]
        action = state_data.get("action")

        if action == "waiting_member_sell_delivery":
            order_id = state_data.get("order_id")
            if message.content_type != "text" or not text.strip():
                bot.reply_to(message, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} ডেলিভারি মেসেজটি Text হিসেবে লিখে পাঠান।", parse_mode="HTML")
                return
            order_row = get_member_sell_order(order_id)
            if not order_row or order_row[8] != "delivering":
                del admin_states[user_id]
                bot.reply_to(message, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} এই অর্ডারটি আর ডেলিভারি অবস্থায় নেই।", parse_mode="HTML")
                return
            target_user = order_row[1]
            delivery_text = text.strip()
            try:
                bot.send_message(
                    target_user,
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['service'])} <b>আপনার Telegram Member Sell অর্ডারটি সম্পন্ন হয়েছে!</b>\n\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['delivery_info'])} <b>অ্যাডমিনের মেসেজ / ডেলিভারি তথ্য:</b>\n{html.escape(delivery_text)}\n\n"
                    f"{member_sell_emoji(MEMBER_SELL_EMOJIS['thanks'])} ধন্যবাদ।",
                    parse_mode="HTML",
                    reply_markup=get_permanent_keyboard(target_user)
                )
            except Exception as e:
                bot.reply_to(message, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} ইউজারের কাছে ডেলিভারি মেসেজ পাঠানো যায়নি: <code>{html.escape(str(e))}</code>\nআবার মেসেজ পাঠানোর চেষ্টা করুন।", parse_mode="HTML")
                return

            conn = db_connect()
            cur = conn.cursor()
            cur.execute(
                "UPDATE member_sell_orders SET status = 'completed', completed_at = ?, delivery_text = ? "
                "WHERE order_id = ? AND status = 'delivering'",
                (datetime.now(timezone.utc).isoformat(), delivery_text, order_id)
            )
            conn.commit()
            conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{member_sell_emoji(MEMBER_SELL_EMOJIS["service"])} অর্ডার <code>{html.escape(order_id)}</code> সফলভাবে Complete হয়েছে এবং ডেলিভারি মেসেজ কাস্টমারের কাছে পাঠানো হয়েছে।", parse_mode="HTML")
            return

        if action == "waiting_other_emoji_code":
            emoji_id_val = (text or "").strip()
            pending_data = state_data.get("pending_btn_data")
            if not (emoji_id_val.isdigit() and 10 <= len(emoji_id_val) <= 30):
                bot.reply_to(message, f"{pe('warn_icon')} সঠিক Custom Emoji ID দিন (১০-৩০ সংখ্যার ID)। আবার পাঠান।", parse_mode="HTML")
                return
            if not pending_data:
                del admin_states[user_id]
                bot.reply_to(message, f"{pe('warn_icon')} এডিট/অ্যাড সেশনটি পাওয়া যায়নি। আবার শুরু করুন।", parse_mode="HTML")
                return
            try:
                _save_pending_button(pending_data, has_emoji=True, custom_emoji_id=emoji_id_val)
                del admin_states[user_id]
                bot.reply_to(
                    message,
                    f"{pe('step_tick')} কাস্টম প্রিমিয়াম ইমোজিসহ বাটনটি সফলভাবে সেভ হয়েছে!\n"
                    f"নাম: <b>{html.escape(str(pending_data.get('name', '')))}</b>\n"
                    f"রেট: <b>৳{float(pending_data.get('price', 0)):g}</b>",
                    parse_mode="HTML"
                )
            except Exception as e:
                print(f"Custom button emoji save error: {e}")
                bot.reply_to(message, f"{pe('warn_icon')} বাটনটি সেভ করা যায়নি: <code>{html.escape(str(e))}</code>", parse_mode="HTML")
            return

        if action == "waiting_premium_emoji_txt":
            mapping, legacy_entries = parse_premium_emoji_mapping(text)
            if not mapping:
                bot.reply_to(message, f"{pe('warn_icon')} সঠিক ফরম্যাটে ইমোজি ও Custom Emoji ID পাঠান। উদাহরণ: <code>🔴 = 5788939937335366</code>", parse_mode="HTML")
                return
            save_premium_emoji_mapping(mapping)
            if legacy_entries:
                conn = db_connect()
                cur = conn.cursor()
                for legacy_key, legacy_id in legacy_entries.items():
                    cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (PREMIUM_EMOJI_PREFIX + legacy_key, legacy_id))
                conn.commit()
                conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{pe('step_tick')} <b>Premium Emoji Set সফলভাবে save হয়েছে!</b>\nBroadcast-এ এখন সাধারণ ইমোজি ব্যবহার করলেই Premium Emoji পাঠানো হবে।", parse_mode="HTML")
            return

        if action == "waiting_delivery_content":
            target_user = state_data["target_user"]
            del admin_states[user_id]
            try:
                bot.send_message(
                    target_user, 
                    f"{pe('order_delivered')} <b>আপনার অর্ডারটি সফলভাবে সম্পন্ন ও ডেলিভারি হয়েছে!</b>\n\n"
                    f"{pe('box_package')} <b>ডিটেইলস / অ্যাকাউন্ট:</b>\n{text}\n\n"
                    f"আমাদের সাথে থাকার জন্য ধন্যবাদ! {pe('welcome_heart')}", 
                    parse_mode="HTML", 
                    reply_markup=get_permanent_keyboard(target_user)
                )
                bot.reply_to(message, f"{pe('step_tick')} সফলভাবে ইউজারের কাছে (ID: <code>{target_user}</code>) অর্ডার ডেলিভারি পাঠানো হয়েছে!", parse_mode="HTML")
            except Exception as e:
                bot.reply_to(message, f"ইউজারের কাছে মেসেজ পাঠানো যায়নি: {e}")
            return

        elif action == "adding_new_cat":
            raw_value = (text or "").strip()
            parts = raw_value.rsplit(None, 1)
            if len(parts) != 2 or not parts[0].strip() or not re.fullmatch(r"(?:\d+(?:\.\d+)?|\.\d+)", parts[1]):
                bot.reply_to(message, f"{pe('warn_icon')} সঠিক ফরম্যাটে নাম ও রেট দিন।\n<b>ফরম্যাট:</b> <code>[Button Name] [Price]</code>\n<b>উদাহরণ:</b> <code>9 Proxy (100MB) 15.0</code>", parse_mode="HTML")
                return
            c_name, c_price = parts[0].strip(), float(parts[1])
            admin_states[user_id] = {
                "action": "waiting_emoji_choice",
                "pending_btn_data": {"mode": "new_cat", "name": c_name, "price": c_price}
            }
            markup = InlineKeyboardMarkup(row_width=3)
            markup.add(
                InlineKeyboardButton("Yes", callback_data="btn_emojichoice_yes"),
                InlineKeyboardButton("No", callback_data="btn_emojichoice_no"),
                InlineKeyboardButton("Other Emoji Code", callback_data="btn_emojichoice_other")
            )
            bot.reply_to(message, f"আপনি কি এই বাটনে প্রিমিয়াম ইমোজি সেট করতে চান?", reply_markup=markup)
            return

        elif action == "waiting_generic_btn_update":
            btn_type, btn_id = state_data.get("btn_type"), str(state_data.get("btn_id"))
            raw_value = (text or "").strip()
            parts = raw_value.rsplit(None, 1)
            if len(parts) != 2 or not parts[0].strip() or not re.fullmatch(r"(?:\d+(?:\.\d+)?|\.\d+)", parts[1]):
                bot.reply_to(
                    message,
                    f"{pe('warn_icon')} সঠিক ফরম্যাটে নতুন নাম ও রেট দিন।\n"
                    f"<b>ফরম্যাট:</b> <code>[নতুন নাম] [নতুন রেট]</code>\n"
                    f"<b>উদাহরণ:</b> <code>9 Proxy (100MB) 15.0</code>",
                    parse_mode="HTML"
                )
                return

            new_name, new_price = parts[0].strip(), float(parts[1])
            if btn_type == "cat":
                pending_data = {"mode": "edit_cat", "cat_id": btn_id, "name": new_name, "price": new_price}
            elif btn_type == "sub":
                pending_data = {"mode": "edit_sub", "sub_id": btn_id, "name": new_name, "price": new_price}
            else:
                bot.reply_to(message, f"{pe('warn_icon')} এই বাটনের ধরনটি এডিট করা যাচ্ছে না।", parse_mode="HTML")
                return

            admin_states[user_id] = {"action": "waiting_emoji_choice", "pending_btn_data": pending_data}
            markup = InlineKeyboardMarkup(row_width=3)
            markup.add(
                InlineKeyboardButton("Yes", callback_data="btn_emojichoice_yes"),
                InlineKeyboardButton("No", callback_data="btn_emojichoice_no"),
                InlineKeyboardButton("Other Emoji Code", callback_data="btn_emojichoice_other")
            )
            bot.reply_to(
                message,
                f"নতুন নাম: <b>{html.escape(new_name)}</b>\nনতুন রেট: <b>৳{new_price:g}</b>\n\n"
                f"এই বাটনে প্রিমিয়াম ইমোজি সেট করতে চান?",
                parse_mode="HTML", reply_markup=markup
            )
            return

        elif action == "waiting_direct_broadcast_message":
            del admin_states[user_id]
            conn = db_connect()
            cursor = conn.cursor()
            cursor.execute("SELECT user_id FROM users")
            target_uids = [row[0] for row in cursor.fetchall()]
            conn.close()
            bot.reply_to(message, f"{pe('waiting_clock')} <b>Broadcast শুরু হয়েছে...</b>", parse_mode="HTML")
            success_count = 0
            premium_mapping = load_premium_emoji_mapping()
            broadcast_text = convert_premium_emoji_text(message.text or "", premium_mapping)
            broadcast_caption = convert_premium_emoji_text(message.caption or "", premium_mapping)
            for target_uid in target_uids:
                try:
                    if message.content_type == 'text':
                        bot.send_message(target_uid, broadcast_text, parse_mode="HTML")
                    elif message.content_type == 'photo':
                        bot.send_photo(target_uid, message.photo[-1].file_id, caption=broadcast_caption, parse_mode="HTML")
                    elif message.content_type == 'voice':
                        bot.send_voice(target_uid, message.voice.file_id, caption=broadcast_caption, parse_mode="HTML")
                    elif message.content_type == 'video':
                        bot.send_video(target_uid, message.video.file_id, caption=broadcast_caption, parse_mode="HTML")
                    elif message.content_type == 'document':
                        bot.send_document(target_uid, message.document.file_id, caption=broadcast_caption, parse_mode="HTML")
                    success_count += 1
                except Exception as e:
                    print(f"Broadcast failed for {target_uid}: {e}")
            bot.send_message(ADMIN_ID, f"{pe('step_tick')} <b>Broadcast সম্পূর্ণ হয়েছে!</b>\nসফলভাবে পাঠানো হয়েছে: <b>{success_count}</b> জন ইউজারের কাছে।", parse_mode="HTML")
            return

        elif action == "waiting_live_broadcast_message":
            target_uids = state_data["target_uids"]
            del admin_states[user_id]

            bot.reply_to(message, f"{pe('waiting_clock')} <b>মেম্বারদের কাছে বার্তা পাঠানো শুরু হচ্ছে...</b>", parse_mode="HTML")

            success_count = 0
            premium_mapping = load_premium_emoji_mapping()
            broadcast_text = convert_premium_emoji_text(message.text or "", premium_mapping)
            broadcast_caption = convert_premium_emoji_text(message.caption or "", premium_mapping)
            for target_uid in target_uids:
                try:
                    if message.content_type == 'text':
                        bot.send_message(target_uid, f"{pe('loudspeaker')} <b>বিশেষ বার্তা:</b>\n\n{broadcast_text}", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_uid))
                    elif message.content_type == 'photo':
                        cap = broadcast_caption
                        bot.send_photo(target_uid, message.photo[-1].file_id, caption=f"{pe('loudspeaker')} <b>বিশেষ বার্তা:</b>\n\n{cap}", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_uid))
                    elif message.content_type == 'voice':
                        bot.send_voice(target_uid, message.voice.file_id, caption=f"{pe('loudspeaker')} <b>অফিসিয়াল ভয়েস বার্তা</b>", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_uid))
                    elif message.content_type == 'video':
                        cap = broadcast_caption
                        bot.send_video(target_uid, message.video.file_id, caption=f"{pe('loudspeaker')} <b>বিশেষ ভিডিও:</b>\n\n{cap}", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_uid))
                    elif message.content_type == 'document':
                        bot.send_document(target_uid, message.document.file_id, caption=f"{pe('loudspeaker')} <b>অফিসিয়াল ফাইল</b>", parse_mode="HTML", reply_markup=get_permanent_keyboard(target_uid))
                    success_count += 1
                except Exception:
                    pass

            bot.send_message(
                ADMIN_ID,
                f"{pe('step_tick')} <b>ব্রডকাস্ট সম্পূর্ণ সফল হয়েছে!</b>\nমোট পাঠানো হয়েছে: <b>{success_count} জন</b> মেম্বারের ইনবক্সে。",
                parse_mode="HTML"
            )
            return

        elif action == "saving_payment_number":
            pmethod = state_data["method"]
            val = message.text.strip()
            key_map = {"bkash": "bkash_num", "nagad": "nagad_num", "rocket": "rocket_num", "binance": "binance_uid"}
            setting_key = key_map.get(pmethod, "bkash_num")
            
            conn = db_connect()
            cur = conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (setting_key, val))
            conn.commit()
            conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{pe('step_tick')} সফলভাবে <b>{pmethod.upper()}</b> আপডেট করা হয়েছে: <code>{val}</code>", parse_mode="HTML")
            return

        elif action == "waiting_pc_directory_path":
            val = message.text.strip()
            conn = db_connect()
            cur = conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('pc_directory_path', ?)", (val,))
            conn.commit()
            conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{pe('step_tick')} পিসি ডিরেক্টরি পাথ সফলভাবে সেভ করা হয়েছে: <code>{val}</code>", parse_mode="HTML")
            return

        elif action == "waiting_pc_live_money_path":
            val = message.text.strip()
            conn = db_connect()
            cur = conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('pc_live_money_path', ?)", (val,))
            conn.commit()
            conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{pe('step_tick')} লাইভ মানি এনালাইসিস ফোল্ডার পাথ সফলভাবে সেভ করা হয়েছে: <code>{val}</code>", parse_mode="HTML")
            return

        elif action == "waiting_pc_live_stock_path":
            val = message.text.strip()
            conn = db_connect()
            cur = conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('pc_live_stock_path', ?)", (val,))
            conn.commit()
            conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{pe('step_tick')} লাইভ স্টক ফোল্ডার পাথ সফলভাবে সেভ করা হয়েছে: <code>{val}</code>", parse_mode="HTML")
            return

        elif action == "waiting_generic_post_update":
            post_key = state_data["post_key"]
            val = message.text
            conn = db_connect()
            cur = conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (post_key, val))
            conn.commit()
            conn.close()
            del admin_states[user_id]
            bot.reply_to(message, f"{pe('step_tick')} সফলভাবে পোস্টটি আপডেট করা হয়েছে!", parse_mode="HTML")
            return

        elif action == "waiting_member_uid_for_balance":
            state_data["target_uid"] = text.strip()
            state_data["action"] = "waiting_member_amount_for_balance"
            bot.reply_to(message, f"{pe('deposit_money')} এই ইউজারের অ্যাকাউন্টে কত টাকা ব্যাক দিতে চাচ্ছেন? সঠিক পরিমাণ (যেমন: <code>50</code>) চ্যাটে লিখে পাঠান:", parse_mode="HTML")
            return

        elif action == "waiting_member_amount_for_balance":
            target_uid_str = state_data["target_uid"]
            del admin_states[user_id]
            try:
                target_uid = int(target_uid_str)
                add_amount = float(text.strip())

                conn = db_connect()
                cursor = conn.cursor()
                cursor.execute("SELECT user_id, balance FROM users WHERE user_id = ?", (target_uid,))
                user_row = cursor.fetchone()

                if user_row:
                    cursor.execute("UPDATE users SET balance = balance + ? WHERE user_id = ?", (add_amount, target_uid))
                    conn.commit()
                    cursor.execute("SELECT balance FROM users WHERE user_id = ?", (target_uid,))
                    new_bal = cursor.fetchone()[0]
                else:
                    cursor.execute("INSERT INTO users (user_id, first_name, balance, username) VALUES (?, ?, ?, 'N/A')", (target_uid, "User", add_amount))
                    conn.commit()
                    new_bal = add_amount
                conn.close()

                try:
                    bot.send_message(
                        target_uid,
                        f"{pe('deposit_success')} <b>বট আপডেট করা হয়েছে!</b>\n\nআপনার একাউন্টে ৳{add_amount} টাকা এড করা হয়েছে।",
                        parse_mode="HTML",
                        reply_markup=get_permanent_keyboard(target_uid)
                    )
                except Exception:
                    pass

                bot.reply_to(message, f"{pe('step_tick')} সফলভাবে ইউজার (<code>{target_uid}</code>) এর অ্যাকাউন্টে ব্যালেন্স <b>৳{add_amount}</b> যোগ করা হয়েছে! নতুন ব্যালেন্স: ৳{new_bal}", parse_mode="HTML")
            except ValueError:
                bot.reply_to(message, f"{pe('warn_icon')} ইউজার আইডি অথবা টাকার পরিমাণ সঠিক সংখ্যায় দিন।", parse_mode="HTML")
            return

        elif action == "waiting_member_uid_for_remove_money":
            target_uid_str = text.strip()
            try:
                target_uid = int(target_uid_str)
                conn = db_connect()
                cursor = conn.cursor()
                cursor.execute("SELECT balance, first_name FROM users WHERE user_id = ?", (target_uid,))
                row = cursor.fetchone()
                conn.close()

                if row:
                    current_bal = row[0]
                    u_name = row[1] or "User"
                    state_data["target_uid"] = target_uid
                    state_data["action"] = "waiting_member_amount_for_remove_money"
                    bot.reply_to(message, f"{pe('profile_user')} ইউজার: <b>{u_name}</b> (ID: <code>{target_uid}</code>)\nবর্তমান ব্যালেন্স: <b>৳{current_bal}</b>\n\nনতুন ব্যালেন্স কত করতে চান তার পরিমাণ লিখে পাঠান:", parse_mode="HTML")
                else:
                    del admin_states[user_id]
                    bot.reply_to(message, f"{pe('warn_icon')} এই ইউজার আইডি দিয়ে ডাটাবেজে কোনো রেকর্ড পাওয়া যায়নি।", parse_mode="HTML")
            except ValueError:
                del admin_states[user_id]
                bot.reply_to(message, f"{pe('warn_icon')} দয়া করে সঠিক সংখ্যায় ইউজার আইডি দিন।", parse_mode="HTML")
            return

        elif action == "waiting_member_amount_for_remove_money":
            target_uid = state_data["target_uid"]
            del admin_states[user_id]
            try:
                new_amount = float(text.strip())
                conn = db_connect()
                cursor = conn.cursor()
                cursor.execute("UPDATE users SET balance = ? WHERE user_id = ?", (new_amount, target_uid))
                conn.commit()
                conn.close()
                bot.reply_to(message, f"{pe('step_tick')} সফলভাবে ইউজার (<code>{target_uid}</code>)-এর অ্যাকাউন্ট ব্যালেন্স এডিট করে <b>৳{new_amount}</b> করা হয়েছে!", parse_mode="HTML")
            except ValueError:
                bot.reply_to(message, f"{pe('warn_icon')} সঠিক সংখ্যা দিন।", parse_mode="HTML")
            return

        elif action == "searching_user":
            del admin_states[user_id]
            target_id_str = text.strip()
            try:
                target_uid = int(target_id_str)
                conn = db_connect()
                cursor = conn.cursor()
                cursor.execute("SELECT user_id, first_name, balance, username FROM users WHERE user_id = ?", (target_uid,))
                user_row = cursor.fetchone()
                conn.close()
                if user_row:
                    u_id, u_name, u_bal, u_user = user_row
                    resp = (
                        f"{pe('profile_user')} <b>User Profile & Details:</b>\n\n"
                        f"{pe('profile_user')} <b>Name:</b> {u_name or 'User'}\n"
                        f"{pe('username_link')} <b>Username:</b> <b>{u_user or 'N/A'}</b>\n"
                        f"{pe('id_badge')} <b>User ID:</b> <code>{u_id}</code>\n"
                        f"{pe('balance_coin')} <b>Account Balance:</b> <b>৳{u_bal}</b> {pe('diamond_badge')}"
                    )
                    bot.reply_to(message, resp, parse_mode="HTML")
                else:
                    bot.reply_to(message, f"{pe('warn_icon')} এই ইউজার আইডি দিয়ে কোনো রেকর্ড পাওয়া যায়নি।", parse_mode="HTML")
            except ValueError:
                bot.reply_to(message, f"{pe('warn_icon')} দয়া করে সঠিক সংখ্যায় ইউজার আইডি দিন।", parse_mode="HTML")
            return

        elif action == "waiting_bulk_money_data":
            try:
                file_info = bot.get_file(message.document.file_id) if message.document else None
                lines = text.splitlines() if not message.document else []
                del admin_states[user_id]
                bot.reply_to(message, f"{pe('step_tick')} বুল্ক ব্যালেন্স আপডেট সফল হয়েছে!", parse_mode="HTML")
            except Exception as e:
                bot.reply_to(message, f"ত্রুটি: {e}")
            return

    if message.content_type == 'photo':
        if user_id in user_temp_deposit and user_temp_deposit[user_id].get("step") == "waiting_screenshot":
            photo_id = message.photo[-1].file_id
            process_deposit_submission(message, photo_id, is_document=False)
            return

@app.route('/')
def home():
    return "Bot is running successfully!"

if __name__ == "__main__":
    # A local OS lock prevents accidental duplicate polling from another copy of this file.
    if not acquire_single_instance_lock():
        raise SystemExit(1)
    # Cluster-wide guard (other servers / Render copies too): only ONE process may poll this token.
    if not pgdb.acquire_polling_lock(int(os.environ.get("POLL_LOCK_WAIT_SECONDS", "90"))):
        print("ERROR: another bot instance (on this or another server) already holds the PostgreSQL polling lock. Stop the old copy first.")
        raise SystemExit(1)

    gw_host = os.environ.get("GATEWAY_HOST", "0.0.0.0")
    gw_port = int(os.environ.get("GATEWAY_PORT") or os.environ.get("PORT") or 5000)
    tls_cert, tls_key = os.environ.get("GATEWAY_TLS_CERT"), os.environ.get("GATEWAY_TLS_KEY")
    public_url = os.environ.get("GATEWAY_PUBLIC_URL", "").strip()

    bot_state = {"running": False, "error": None}

    def run_bot():
        try:
            bot.get_me()  # proves the token works before we say RUNNING
            # This bot uses polling. Remove any old webhook once, before starting polling.
            bot.remove_webhook()
            bot_state["running"] = True
            while True:
                try:
                    bot.infinity_polling(none_stop=False, interval=0, timeout=20, long_polling_timeout=20)
                    # A clean return is unusual; wait briefly before reconnecting.
                    time.sleep(1)
                except Exception as e:
                    error_code = getattr(e, "error_code", None)
                    error_text = str(e)
                    if error_code == 409 or "409" in error_text or "terminated by other getUpdates request" in error_text:
                        bot_state["running"] = False
                        bot_state["error"] = error_text
                        print(
                            "FATAL: Telegram rejected polling because another process/server is using this bot token. "
                            "Stop every old bot instance (including VPS/Render copies) and run only one instance. "
                            f"Details: {error_text}"
                        )
                        return
                    print(f"Polling crashed: {error_text}")
                    time.sleep(3)
        except Exception as e:
            bot_state["error"] = str(e)
            print(f"Bot polling could not start: {e}")

    t_bot = threading.Thread(target=run_bot, name="telegram-polling", daemon=True)
    t_bot.start()

    t_backup = threading.Thread(target=auto_drive_backup_loop, daemon=True)
    t_backup.start()

    gw_ok, gw_detail = pgw.start_gateway_server(app, gw_host, gw_port, tls_cert, tls_key)
    pgw.start_reconciler()
    for _ in range(100):  # wait up to ~10s for the Telegram check
        if bot_state["running"] or bot_state["error"]:
            break
        time.sleep(0.1)

    print("TELEGRAM BOT: " + ("RUNNING" if bot_state["running"] else f"FAILED ({bot_state['error']})"))
    print("SMS GATEWAY: " + (f"RUNNING ({gw_detail})" if gw_ok else f"FAILED ({gw_detail})"))
    print("DATABASE: " + pgdb.health()[1])
    print(f"GATEWAY HOST: {gw_host}")
    print(f"GATEWAY PORT: {gw_port}")
    print("PUBLIC GATEWAY URL: " + (public_url or "NOT CONFIGURED (set GATEWAY_PUBLIC_URL)"))
    if gw_ok and not (tls_cert and tls_key):
        print("WARNING: gateway is plain HTTP. The Android app only accepts HTTPS - put nginx/Caddy with a TLS certificate in front (see README_DEPLOYMENT.md).")
    print("PAYMENT RECONCILIATION: ACTIVE (every %ss)" % pgw.RECONCILE_INTERVAL)
    if pgw.binance_history_configured():
        _bok, _bmsg = pgw.binance_selftest()
        print("BINANCE API CHECK: " + ("OK" if _bok else "FAILED") + " - " + _bmsg)
    print("SMS devices registered: " + str(pgw.admin_stats()["devices"]) + " | Binance merchant API: " + ("configured" if pgw.merchant_configured() else "not configured") + " | Binance UID check: " + ("configured" if pgw.binance_history_configured() else "not configured"))

    if not gw_ok:
        raise SystemExit(1)
    while True:  # keep the main thread alive; both services run in their own threads
        time.sleep(3600)
