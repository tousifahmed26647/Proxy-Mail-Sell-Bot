#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
migrate_sqlite_to_pg.py - one-time, SAFE cut-over of the old SQLite-primary bot to PostgreSQL-primary.

Where the old data is:
  * the old bot kept the live data in shop_bot.db (SQLite) and mirrored the WHOLE FILE as a single BYTEA
    blob into PostgreSQL table  bot_sqlite_backup (id=1).  That blob is what "my existing PostgreSQL data"
    really is: there were no real tables in PostgreSQL before.
  * this tool reads that blob (or a shop_bot.db file you give it) and copies the rows into real tables.

Guarantees
  * NEVER drops / truncates / deletes / overwrites. Only INSERT ... ON CONFLICT DO NOTHING.
  * A row already present in PostgreSQL is kept as is, even if the SQLite copy differs (reported as a conflict).
  * Idempotent: running it twice inserts nothing the second time.
  * Dry-run is the default. --apply needs a verified pg_dump file (--backup-file) and the bot must be stopped.
  * Every user balance that is inserted gets an 'opening balance' ledger row (via the DB trigger).
  * Writes a JSON report (counts, conflicts, inserted keys) and exits non-zero if any verification FAILS.

Usage
  python migrate_sqlite_to_pg.py --inspect
  python migrate_sqlite_to_pg.py --source pg-blob                      # dry-run (default)
  python migrate_sqlite_to_pg.py --source sqlite --path shop_bot.db    # dry-run from a file
  python migrate_sqlite_to_pg.py --source pg-blob --apply --backup-file backups/pre_migration.dump
"""
import argparse
import json
import os
import sqlite3
import sys
import tempfile
import time
from decimal import Decimal

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
# ---- end embedded modules ----

# table -> (primary-key column, identity column or None). Order matters (parents first).
TABLES = [
    ("users", "user_id", None),
    ("categories", "cat_id", None),
    ("sub_services", "sub_id", "sub_id"),
    ("stock", "id", "id"),
    ("stock_sales", "sale_id", "sale_id"),
    ("referral_deposit_bonus_ledger", "bonus_id", "bonus_id"),
    ("custom_buttons", "id", "id"),
    ("member_sell_orders", "order_id", None),
    ("settings", "key", None),
    ("pending_deposits", "id", "id"),
    ("payment_transactions", "id", "id"),
    ("payment_events", "id", "id"),
    ("payment_settings", "key", None),
    ("payment_audit_logs", "id", "id"),
    ("api_devices", "id", "id"),
    ("binance_orders", "id", "id"),
]
MONEY_COLS = {"users": "balance"}


def log(msg):
    print(msg, flush=True)


def pg_columns(c, table):
    rows = c.execute("SELECT column_name FROM information_schema.columns WHERE table_schema=current_schema() "
                     "AND table_name=? ORDER BY ordinal_position", (table,)).fetchall()
    return [r[0] for r in rows]


def pg_count(c, table):
    return c.execute('SELECT COUNT(*) FROM "%s"' % table).fetchone()[0]


# --------------------------------------------------------------------------- source
def open_source(args):
    if args.source == "sqlite":
        path = args.path
        if not path or not os.path.exists(path):
            sys.exit("SQLite file not found: %r" % path)
        origin = "file " + path
    else:
        c = pgdb.connect()
        try:
            has = c.execute("SELECT to_regclass('bot_sqlite_backup')").fetchone()[0]
            if not has:
                sys.exit("No bot_sqlite_backup table in PostgreSQL: nothing to migrate from. Use --source sqlite --path <file>.")
            row = c.execute("SELECT db_data, updated_at FROM bot_sqlite_backup WHERE id = 1").fetchone()
        finally:
            c.close()
        if not row:
            sys.exit("bot_sqlite_backup has no row id=1.")
        os.makedirs("backups", exist_ok=True)
        path = os.path.join("backups", "shop_bot_from_pg_%s.db" % time.strftime("%Y%m%d_%H%M%S"))
        with open(path, "wb") as f:
            f.write(bytes(row[0]))
        origin = "PostgreSQL blob bot_sqlite_backup (updated_at %s) saved to %s (%d bytes)" % (row[1], path, len(bytes(row[0])))
    src = sqlite3.connect("file:%s?mode=ro" % os.path.abspath(path), uri=True)  # read-only archive source
    src.row_factory = sqlite3.Row
    ok = src.execute("PRAGMA integrity_check").fetchone()[0]
    if ok != "ok":
        sys.exit("SQLite source failed integrity_check: %s" % ok)
    return src, origin


def src_tables(src):
    return {r[0] for r in src.execute("SELECT name FROM sqlite_master WHERE type='table'")}


# --------------------------------------------------------------------------- inspect
def inspect():
    c = pgdb.connect()
    try:
        print("== PostgreSQL inspection (credentials never printed) ==")
        print(pgdb.health()[1])
        tabs = [r[0] for r in c.execute("SELECT table_name FROM information_schema.tables WHERE table_schema=current_schema() "
                                         "AND table_type='BASE TABLE' ORDER BY 1").fetchall()]
        for t in tabs:
            print("  %-34s rows=%s" % (t, pg_count(c, t)))
        blob = c.execute("SELECT to_regclass('bot_sqlite_backup')").fetchone()[0]
        if blob:
            r = c.execute("SELECT length(db_data), updated_at FROM bot_sqlite_backup WHERE id=1").fetchone()
            print("legacy blob bot_sqlite_backup: %s" % (("%d bytes, updated_at %s" % (r[0], r[1])) if r else "empty"))
        print("indexes:", c.execute("SELECT COUNT(*) FROM pg_indexes WHERE schemaname=current_schema()").fetchone()[0],
              "| constraints:", c.execute("SELECT COUNT(*) FROM pg_constraint c JOIN pg_namespace n ON n.oid=c.connamespace "
                                           "WHERE n.nspname=current_schema()").fetchone()[0])
        for t, _pk, idc in TABLES:
            if idc and t in tabs:
                seq = c.execute("SELECT pg_get_serial_sequence(?, ?)", (t, idc)).fetchone()[0]
                print("  sequence %-40s %s" % (t + "." + idc, seq))
    finally:
        c.close()


# --------------------------------------------------------------------------- migrate
def to_pg_value(v):
    if isinstance(v, float):
        return Decimal(repr(v))
    if isinstance(v, bytes):
        return v.decode("utf-8", "replace")
    return v


def migrate(src, apply_changes, report):
    stabs = src_tables(src)
    conn = pgdb.connect()
    try:
        for table, pk, idc in TABLES:
            if table not in stabs:
                report["tables"][table] = {"source_rows": 0, "note": "not present in source"}
                continue
            pcols = pg_columns(conn, table)
            if not pcols:
                sys.exit("PostgreSQL table %s is missing - run the migrations first (python -c 'import pgdb;pgdb.apply_migrations()')" % table)
            srows = src.execute('SELECT * FROM "%s"' % table).fetchall()
            scols = [d[0] for d in src.execute('SELECT * FROM "%s" LIMIT 0' % table).description]
            cols = [c for c in scols if c in pcols]
            dropped = [c for c in scols if c not in pcols]
            info = {"source_rows": len(srows), "pg_rows_before": pg_count(conn, table), "inserted": 0,
                    "already_present_identical": 0, "conflicts_pg_kept": [], "skipped_columns": dropped, "inserted_keys": []}
            ins_sql = 'INSERT INTO "%s" (%s) VALUES (%s) ON CONFLICT DO NOTHING' % (
                table, ",".join('"%s"' % c for c in cols), ",".join(["%s"] * len(cols)))
            raw = conn._raw  # use psycopg directly: statements here are already PostgreSQL SQL
            for r in srows:
                vals = [to_pg_value(r[c]) for c in cols]
                key = r[pk] if pk in r.keys() else None
                if table == "users":
                    raw.execute("SELECT set_config('app.ledger_reason','migration_opening_balance',true), "
                                "set_config('app.ledger_ref',%s,true), set_config('app.ledger_actor','migration',true)",
                                ("opening:%s" % key,))
                cur = raw.execute(ins_sql, vals)
                if cur.rowcount == 1:
                    info["inserted"] += 1
                    info["inserted_keys"].append(key)
                else:  # something already there: never overwrite, just compare
                    ex = raw.execute('SELECT * FROM "%s" WHERE "%s" = %%s' % (table, pk), (key,)).fetchone()
                    if ex is None:
                        info["conflicts_pg_kept"].append({"key": key, "why": "unique-constraint conflict on another column"})
                        continue
                    diff = [c for c in cols if str(ex[pcols.index(c)]) != str(to_pg_value(r[c])) and not _num_equal(ex[pcols.index(c)], r[c])]
                    if diff:
                        info["conflicts_pg_kept"].append({"key": key, "columns_differ": diff})
                    else:
                        info["already_present_identical"] += 1
            if table == "users":
                raw.execute("SELECT set_config('app.ledger_reason','',true), set_config('app.ledger_ref','',true), set_config('app.ledger_actor','',true)")
            report["tables"][table] = info
            log("  %-32s source=%-6d inserted=%-6d identical=%-6d conflicts(kept PG)=%d" % (
                table, len(srows), info["inserted"], info["already_present_identical"], len(info["conflicts_pg_kept"])))
        if apply_changes:
            for table, pk, idc in TABLES:  # sequences must continue after the highest migrated id
                if idc and report["tables"].get(table, {}).get("source_rows"):
                    conn._raw.execute("SELECT setval(pg_get_serial_sequence(%s, %s), COALESCE((SELECT MAX(" + idc + ") FROM " + table + "), 1), true)",
                                      (table, idc))
            conn.commit()
        else:
            conn.rollback()
    except BaseException:
        conn.rollback()
        raise
    finally:
        conn.close()


def _num_equal(a, b):
    try:
        return abs(Decimal(str(a)) - Decimal(repr(b) if isinstance(b, float) else str(b))) < Decimal("0.0001")
    except Exception:
        return False


# --------------------------------------------------------------------------- verification
def verify(src, report):
    checks = []

    def chk(name, ok, detail=""):
        checks.append({"check": name, "result": "PASS" if ok else "FAIL", "detail": detail})
        log("  [%s] %s %s" % ("PASS" if ok else "FAIL", name, detail))

    c = pgdb.connect()
    try:
        stabs = src_tables(src)
        for table, pk, idc in TABLES:
            if table in stabs:
                s_n = src.execute('SELECT COUNT(*) FROM "%s"' % table).fetchone()[0]
                p_n = pg_count(c, table)
                chk("row count %s (PG >= source)" % table, p_n >= s_n, "source=%d pg=%d" % (s_n, p_n))
        if "users" in stabs:
            s_sum = Decimal(str(src.execute("SELECT COALESCE(SUM(balance),0) FROM users").fetchone()[0])).quantize(Decimal("0.01"))
            p_sum = Decimal(str(c.execute("SELECT COALESCE(SUM(balance),0) FROM users").fetchone()[0])).quantize(Decimal("0.01"))
            n_conf = len(report["tables"].get("users", {}).get("conflicts_pg_kept", []))
            chk("sum(users.balance) equals source" if n_conf == 0 else "sum(users.balance) (conflicts exist, PG values kept)",
                s_sum == p_sum or n_conf > 0, "source=%s pg=%s" % (s_sum, p_sum))
        if "pending_deposits" in stabs:
            for st, tot in src.execute("SELECT status, COALESCE(SUM(amount_minor),0) FROM pending_deposits GROUP BY status"):
                pt = c.execute("SELECT COALESCE(SUM(amount_minor),0) FROM pending_deposits WHERE status=?", (st,)).fetchone()[0]
                chk("deposit total status=%s" % st, pt >= tot, "source=%s pg=%s" % (tot, pt))
        dup = c.execute("SELECT COUNT(*) FROM (SELECT 1 FROM payment_transactions GROUP BY provider, provider_trx_id HAVING COUNT(*)>1) x").fetchone()[0]
        chk("no duplicate provider transactions", dup == 0, "duplicates=%d" % dup)
        dup2 = c.execute("SELECT COUNT(*) FROM (SELECT 1 FROM pending_deposits WHERE status='APPROVED' GROUP BY provider, provider_trx_id HAVING COUNT(*)>1) x").fetchone()[0]
        chk("no TrxID approved for two deposits", dup2 == 0, "duplicates=%d" % dup2)
        dup3 = c.execute("SELECT COUNT(*) FROM (SELECT 1 FROM users GROUP BY user_id HAVING COUNT(*)>1) x").fetchone()[0]
        chk("no duplicate users", dup3 == 0)
        bad = c.execute("SELECT COUNT(*) FROM ledger_reconciliation WHERE diff <> 0").fetchone()[0]
        chk("ledger == balance for every user", bad == 0, "mismatching users=%d" % bad)
        orphan = c.execute("SELECT COUNT(*) FROM payment_transactions t LEFT JOIN pending_deposits d ON d.id=t.matched_deposit_id "
                           "WHERE t.matched_deposit_id IS NOT NULL AND d.id IS NULL").fetchone()[0]
        chk("payment->deposit links resolve (foreign keys)", orphan == 0, "orphans=%d" % orphan)
        for table, pk, idc in TABLES:
            if idc:
                mx = c.execute('SELECT COALESCE(MAX("%s"),0) FROM "%s"' % (idc, table)).fetchone()[0]
                ok = True
                if mx:
                    last = c.execute("SELECT pg_sequence_last_value(pg_get_serial_sequence(?,?)::regclass)", (table, idc)).fetchone()[0]
                    ok = (last or 0) >= mx
                chk("sequence %s.%s >= max id" % (table, idc), ok)
    finally:
        c.close()
    report["verification"] = checks
    return all(x["result"] == "PASS" for x in checks)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--inspect", action="store_true", help="only print what is in PostgreSQL")
    ap.add_argument("--source", choices=["pg-blob", "sqlite"], default="pg-blob")
    ap.add_argument("--path", help="shop_bot.db path when --source sqlite")
    ap.add_argument("--apply", action="store_true", help="really write (default is dry-run)")
    ap.add_argument("--backup-file", help="a verified pg_dump file; REQUIRED with --apply")
    args = ap.parse_args()

    if not pgdb.configured():
        sys.exit("DATABASE_URL is not set (.env).")
    pgdb.init()
    if args.inspect:
        inspect()
        return 0

    if args.apply:
        if not args.backup_file or not os.path.exists(args.backup_file) or os.path.getsize(args.backup_file) < 1024:
            sys.exit("--apply requires --backup-file pointing to a real pg_dump (see backup.sh). Refusing.")
        lock = pgdb.acquire_polling_lock(wait_seconds=0)
        if not lock:
            sys.exit("The bot appears to be running (polling lock held). STOP the bot before migrating.")

    log("== applying schema migrations (non-destructive, idempotent) ==")
    log("   applied now: %s" % (pgdb.apply_migrations() or "nothing (already up to date)"))
    src, origin = open_source(args)
    log("== source: %s" % origin)
    report = {"started": time.strftime("%Y-%m-%d %H:%M:%S"), "mode": "APPLY" if args.apply else "DRY-RUN",
              "source": origin, "tables": {}}
    log("== %s ==" % report["mode"])
    migrate(src, args.apply, report)
    ok = True
    if args.apply:
        log("== verification ==")
        ok = verify(src, report)
    else:
        log("(dry-run: nothing was written; re-run with --apply --backup-file <dump> to migrate)")
    os.makedirs("backups", exist_ok=True)
    rp = os.path.join("backups", "migration_report_%s_%s.json" % (report["mode"].lower(), time.strftime("%Y%m%d_%H%M%S")))
    with open(rp, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, default=str)
    log("report: %s" % rp)
    n_conf = sum(len(t.get("conflicts_pg_kept", [])) for t in report["tables"].values())
    if n_conf:
        log("!! %d conflicting row(s): PostgreSQL value was KEPT (nothing overwritten). Review the report." % n_conf)
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
