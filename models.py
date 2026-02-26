"""
models.py — Database Models & Connection Pool
=============================================
Version 2.0 — Enterprise OTA Platform

Responsibilities:
  - PostgreSQL connection pool (psycopg2 ThreadedConnectionPool)
  - DB health check
  - Schema version tracking
  - Model constants / enums used across services

Connection pool:
  - Pool size: min=2, max=20 (configurable via env)
  - Returns connections with context manager support
  - Automatically returns connections on exit
  - Logs slow queries (> SLOW_QUERY_MS threshold)

Usage in routes:
    from models import db_pool

    with db_pool.get_connection() as conn:
        # conn is a psycopg2 connection
        # automatically returned to pool on exit
        do_something(conn)

Scalability note:
  psycopg2.ThreadedConnectionPool is fine for gunicorn --workers=1 --threads=N
  For multi-process gunicorn (N workers), use pgbouncer or psycopg2 async,
  or migrate to SQLAlchemy with a NullPool + external connection pooler.
"""

from __future__ import annotations

import logging
import os
import time
from contextlib import contextmanager
from typing import Optional

import psycopg2
import psycopg2.extras
from psycopg2 import pool as pg_pool

logger = logging.getLogger(__name__)


# =====================================================
# CONSTANTS / ENUMS
# =====================================================

# Hotel types
HOTEL_TYPES = ('STANDARD', 'BOUTIQUE', 'RESORT', 'HERITAGE', 'BUDGET', 'LUXURY')

# Destination types (mirrors DB CHECK constraint)
DESTINATION_TYPES = (
    'CITY', 'HILL_STATION', 'BEACH', 'RELIGIOUS',
    'ADVENTURE', 'WILDLIFE', 'HERITAGE', 'OTHER'
)

# Addon pricing basis
ADDON_PRICING_BASIS = ('per_person', 'per_booking', 'per_night', 'per_vehicle')

# Transport pricing types
TRANSPORT_PRICING_TYPES = ('per_person', 'per_vehicle')

# Trip types
TRIP_TYPES = ('one_way', 'return', 'both')

# Seasons (legacy — kept for backward compatibility)
SEASONS = ('ON', 'OFF')

# Slow query threshold (ms)
SLOW_QUERY_MS = int(os.environ.get('SLOW_QUERY_MS', '500'))


# =====================================================
# CONNECTION POOL
# =====================================================

class DatabasePool:
    """
    Thread-safe PostgreSQL connection pool wrapper.

    Configuration via environment variables:
      DATABASE_URL    — Full connection URI (preferred)
      DB_HOST         — Fallback individual params
      DB_PORT
      DB_NAME
      DB_USER
      DB_PASSWORD
      DB_POOL_MIN     — Min pool size (default: 2)
      DB_POOL_MAX     — Max pool size (default: 20)
      DB_CONNECT_TIMEOUT — Connection timeout in seconds (default: 10)
    """

    def __init__(self):
        self._pool: Optional[pg_pool.ThreadedConnectionPool] = None

    def init(self) -> None:
        """Initialize the connection pool. Call once at application startup."""
        if self._pool is not None:
            return

        dsn = self._build_dsn()
        min_conn = int(os.environ.get('DB_POOL_MIN', '2'))
        max_conn = int(os.environ.get('DB_POOL_MAX', '20'))

        try:
            self._pool = pg_pool.ThreadedConnectionPool(
                minconn=min_conn,
                maxconn=max_conn,
                dsn=dsn,
                connect_timeout=int(os.environ.get('DB_CONNECT_TIMEOUT', '10')),
                cursor_factory=psycopg2.extras.RealDictCursor,
            )
            logger.info(
                f"DB pool initialized | min={min_conn} max={max_conn} | "
                f"host={os.environ.get('DB_HOST', 'via DATABASE_URL')}"
            )
        except psycopg2.OperationalError as e:
            logger.critical(f"DB pool initialization failed: {e}")
            raise

    @staticmethod
    def _build_dsn() -> str:
        """Build PostgreSQL DSN from env vars."""
        if os.environ.get('DATABASE_URL'):
            return os.environ['DATABASE_URL']

        required = ['DB_HOST', 'DB_NAME', 'DB_USER', 'DB_PASSWORD']
        missing  = [r for r in required if not os.environ.get(r)]
        if missing:
            raise EnvironmentError(
                f"Missing DB env vars: {missing}. "
                "Set DATABASE_URL or individual DB_HOST/DB_NAME/DB_USER/DB_PASSWORD."
            )

        return (
            f"host={os.environ['DB_HOST']} "
            f"port={os.environ.get('DB_PORT', '5432')} "
            f"dbname={os.environ['DB_NAME']} "
            f"user={os.environ['DB_USER']} "
            f"password={os.environ['DB_PASSWORD']}"
        )

    @contextmanager
    def get_connection(self):
        """
        Context manager that gets a connection from the pool
        and returns it automatically on exit.

        Usage:
            with db_pool.get_connection() as conn:
                with conn.cursor() as cur:
                    cur.execute(...)
        """
        if self._pool is None:
            self.init()

        conn = self._pool.getconn()
        try:
            conn.autocommit = False
            yield conn
        except Exception:
            try:
                conn.rollback()
            except Exception:
                pass
            raise
        finally:
            try:
                self._pool.putconn(conn)
            except Exception as e:
                logger.warning(f"Error returning connection to pool: {e}")

    def get_raw_connection(self):
        """
        Get a raw connection from pool (caller responsible for return).
        Prefer get_connection() context manager instead.
        """
        if self._pool is None:
            self.init()
        conn = self._pool.getconn()
        conn.autocommit = False
        return conn

    def return_connection(self, conn, close: bool = False) -> None:
        """Return a raw connection to the pool."""
        if self._pool:
            self._pool.putconn(conn, close=close)

    def health_check(self) -> dict:
        """Check DB connectivity and return status dict."""
        try:
            with self.get_connection() as conn:
                t0 = time.monotonic()
                with conn.cursor() as cur:
                    cur.execute('SELECT 1 AS ping, NOW() AS ts')
                    row = cur.fetchone()
                latency_ms = int((time.monotonic() - t0) * 1000)
            return {
                'status': 'ok',
                'latency_ms': latency_ms,
                'server_ts': str(row['ts']),
                'pool_min': self._pool.minconn if self._pool else 0,
                'pool_max': self._pool.maxconn if self._pool else 0,
            }
        except Exception as e:
            return {'status': 'error', 'detail': str(e)}

    def close(self) -> None:
        """Close all pool connections. Call on application shutdown."""
        if self._pool:
            self._pool.closeall()
            self._pool = None
            logger.info("DB pool closed.")


# =====================================================
# SLOW QUERY LOGGER
# =====================================================

class SlowQueryLogger:
    """
    Wraps a psycopg2 cursor to log queries exceeding SLOW_QUERY_MS.
    Usage: cursor = SlowQueryLogger(conn.cursor())
    Future: integrate with APM (Datadog, New Relic) via custom metrics.
    """
    def __init__(self, cursor, threshold_ms: int = SLOW_QUERY_MS):
        self._cur = cursor
        self._threshold = threshold_ms

    def execute(self, query: str, params=None):
        t0 = time.monotonic()
        self._cur.execute(query, params)
        elapsed = (time.monotonic() - t0) * 1000
        if elapsed > self._threshold:
            short_q = query[:120].replace('\n', ' ')
            logger.warning(f"SLOW QUERY ({elapsed:.0f}ms): {short_q}")

    def __getattr__(self, name):
        return getattr(self._cur, name)


# =====================================================
# SCHEMA VERSION TRACKING
# =====================================================

SCHEMA_VERSION = '5.1'

SCHEMA_VERSION_TABLE = """
CREATE TABLE IF NOT EXISTS schema_versions (
    id SERIAL PRIMARY KEY,
    version VARCHAR(20) NOT NULL,
    applied_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    notes TEXT
);
"""


def record_schema_version(conn, version: str = SCHEMA_VERSION, notes: str = '') -> None:
    """Record a schema migration version. Called by startup migration scripts."""
    try:
        with conn.cursor() as cur:
            cur.execute(SCHEMA_VERSION_TABLE)
            cur.execute(
                "INSERT INTO schema_versions (version, notes) VALUES (%s, %s)",
                (version, notes),
            )
        conn.commit()
        logger.info(f"Schema version {version} recorded.")
    except Exception as e:
        conn.rollback()
        logger.warning(f"Schema version recording failed: {e}")


def get_schema_version(conn) -> Optional[str]:
    """Get the latest recorded schema version."""
    try:
        with conn.cursor() as cur:
            cur.execute(SCHEMA_VERSION_TABLE)
            cur.execute(
                "SELECT version FROM schema_versions ORDER BY applied_at DESC LIMIT 1"
            )
            row = cur.fetchone()
        conn.commit()
        return row['version'] if row else None
    except Exception:
        return None


# =====================================================
# SINGLETON POOL INSTANCE
# =====================================================

db_pool = DatabasePool()
"""
Singleton DB pool. Import this in app.py and services.
Initialize once at startup:

    from models import db_pool
    db_pool.init()
"""