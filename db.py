"""
db.py — permanent storage for the Free Fire bot.

Keep this file next to bot.py. You can replace bot.py as often as you like: everything lives in
./data/ffbot.db (SQLite, created automatically), so tracked players, their history, alert settings
and the premium-emoji map survive updates.

Stored here
  • tracks  : every tracked player (subscribers, alert prefs, baseline, change history…)
  • emojis  : premium emoji map  (char -> custom emoji id)

Premium emojis
  Put emoji.txt (lines like  <tg-emoji emoji-id="123">😀</tg-emoji> ) next to bot.py.
  It is imported into the DB on every start, and stays in the DB even if you delete the txt later.

Env vars (all optional)
  DATA_DIR    folder for the database           (default: ./data next to this file)
  DB_FILE     full path of the sqlite file      (default: DATA_DIR/ffbot.db)
  EMOJI_FILE  path of emoji.txt                 (default: emoji.txt next to this file)
  MONGO_URI   if set, tracks go to MongoDB instead (use this on hosts with a wiped disk, e.g. Render free)

CLI
  python db.py stats            what is stored
  python db.py backup out.json  dump everything to a json file
  python db.py restore in.json  load a backup (replaces tracks, merges emojis)
"""
import asyncio
import json
import logging
import os
import re
import sqlite3
import sys
import threading

log = logging.getLogger("ffinfo.db")

BASE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.getenv("DATA_DIR", os.path.join(BASE, "data"))
DB_FILE = os.getenv("DB_FILE", os.path.join(DATA_DIR, "ffbot.db"))
EMOJI_FILE = os.getenv("EMOJI_FILE", os.path.join(BASE, "emoji.txt"))
MONGO_URI = os.getenv("MONGO_URI", "")

_lock = threading.Lock()
_conn = None
_mcol = None

_EMOJI_RE = re.compile(r'<tg-emoji\s+emoji-id="(\d+)"\s*>(.*?)</tg-emoji>', re.S)


def norm(ch: str) -> str:
    """Emoji key: variation selector removed, so '❤️' and '❤' match."""
    return (ch or "").replace("\ufe0f", "").strip()


def _db():
    global _conn
    if _conn is None:
        os.makedirs(os.path.dirname(os.path.abspath(DB_FILE)), exist_ok=True)
        _conn = sqlite3.connect(DB_FILE, check_same_thread=False, timeout=30)
        try:
            _conn.execute("PRAGMA journal_mode=WAL")
        except Exception:
            pass
        _conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS tracks (uid TEXT PRIMARY KEY, data TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS emojis (ch TEXT PRIMARY KEY, id TEXT NOT NULL);
            CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT);
            """
        )
        _conn.commit()
    return _conn


# ───────────────────────── emojis ─────────────────────────
def parse_emoji_text(txt: str) -> dict:
    out = {}
    for eid, ch in _EMOJI_RE.findall(txt or ""):
        out.setdefault(norm(ch), eid)  # first id wins when a char appears twice
    return out


def import_emoji_file(path=None) -> int:
    path = path or EMOJI_FILE
    if not os.path.exists(path):
        return 0
    with open(path, encoding="utf-8") as f:
        found = parse_emoji_text(f.read())
    if not found:
        return 0
    with _lock:
        c = _db()
        c.executemany("INSERT OR REPLACE INTO emojis(ch,id) VALUES(?,?)", list(found.items()))
        c.commit()
    return len(found)


def get_emojis() -> dict:
    """char -> custom emoji id. Imports emoji.txt first if it exists."""
    try:
        n = import_emoji_file()
        if n:
            log.info("imported %d premium emoji from %s", n, os.path.basename(EMOJI_FILE))
    except Exception as e:
        log.warning("emoji import failed: %r", e)
    with _lock:
        return {ch: i for ch, i in _db().execute("SELECT ch,id FROM emojis")}


# ───────────────────────── tracks ─────────────────────────
def _mongo_col():
    global _mcol
    if _mcol is None and MONGO_URI:
        try:
            from motor.motor_asyncio import AsyncIOMotorClient

            _mcol = AsyncIOMotorClient(MONGO_URI, serverSelectionTimeoutMS=8000)[os.getenv("MONGO_DB", "ffbot")]["tracks"]
        except Exception as e:
            log.warning("MongoDB unavailable (%r) - using sqlite %s", e, DB_FILE)
    return _mcol


def _legacy_json():
    """Old tracks.json from the previous version -> imported once into an empty DB."""
    for p in (os.getenv("TRACK_FILE", ""), "tracks.json", os.path.join(BASE, "tracks.json")):
        if p and os.path.exists(p):
            try:
                with open(p, encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
    return {}


def _load_sql() -> dict:
    with _lock:
        c = _db()
        rows = c.execute("SELECT uid,data FROM tracks").fetchall()
        if not rows and not c.execute("SELECT v FROM meta WHERE k='legacy_imported'").fetchone():
            legacy = _legacy_json()
            c.execute("INSERT OR REPLACE INTO meta(k,v) VALUES('legacy_imported','1')")
            if legacy:
                c.executemany("INSERT OR REPLACE INTO tracks(uid,data) VALUES(?,?)",
                              [(str(u), json.dumps(t, ensure_ascii=False)) for u, t in legacy.items()])
                log.info("imported %d player(s) from old tracks.json", len(legacy))
            c.commit()
            rows = c.execute("SELECT uid,data FROM tracks").fetchall()
    out = {}
    for u, d in rows:
        try:
            out[u] = json.loads(d)
        except Exception:
            continue
    return out


def _save_sql(payload: dict):
    with _lock:
        c = _db()
        have = {r[0] for r in c.execute("SELECT uid FROM tracks")}
        gone = [(u,) for u in have if u not in payload]
        with c:  # one transaction -> never a half-written state
            if gone:
                c.executemany("DELETE FROM tracks WHERE uid=?", gone)
            c.executemany("INSERT OR REPLACE INTO tracks(uid,data) VALUES(?,?)",
                          [(str(u), json.dumps(t, ensure_ascii=False)) for u, t in payload.items()])


async def load_tracks() -> dict:
    col = _mongo_col()
    if col is not None:
        doc = await col.find_one({"_id": "main"})
        return (doc or {}).get("data") or {}
    return await asyncio.to_thread(_load_sql)


async def save_tracks(payload: dict):
    col = _mongo_col()
    if col is not None:
        await col.replace_one({"_id": "main"}, {"data": payload}, upsert=True)
        return
    await asyncio.to_thread(_save_sql, payload)


def backend() -> str:
    return "mongodb" if _mongo_col() is not None else DB_FILE


# ───────────────────────── CLI ─────────────────────────
def _cli(argv):
    cmd = argv[1] if len(argv) > 1 else "stats"
    if cmd == "stats":
        tr = _load_sql()
        em = get_emojis()
        print(f"database : {DB_FILE}")
        print(f"players  : {len(tr)}")
        for u, t in tr.items():
            print(f"  {u}  subs={len(t.get('subs', []))}  changes={t.get('n', 0)}  name={t.get('name', '')[:30]!r}")
        print(f"emojis   : {len(em)}")
    elif cmd == "backup" and len(argv) > 2:
        data = {"tracks": _load_sql(), "emojis": get_emojis()}
        with open(argv[2], "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        print("saved", argv[2])
    elif cmd == "restore" and len(argv) > 2:
        with open(argv[2], encoding="utf-8") as f:
            data = json.load(f)
        _save_sql(data.get("tracks") or {})
        with _lock:
            c = _db()
            c.executemany("INSERT OR REPLACE INTO emojis(ch,id) VALUES(?,?)", list((data.get("emojis") or {}).items()))
            c.commit()
        print("restored", len(data.get("tracks") or {}), "players")
    else:
        print(__doc__)


if __name__ == "__main__":
    _cli(sys.argv)
