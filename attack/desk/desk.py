#!/usr/bin/env python3
"""File-based local desk for the GOLDBACH ATTACK framework.

Commands: next, beat, release, submit, status, blockers.

The desk owns leases only.  It never runs the checker: submission records a
file path and its sha256, and the parent (or another agent) verifies it with
checker/check.py.  All state is human-readable JSON/JSONL.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import sys
import uuid
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterator

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

LEASE_MINUTES = 45
MAX_BEATS = 12


class DeskError(Exception):
    """A user-facing error (printed as 'error: ...', no traceback)."""


def _path_from_env(name: str, default: Path) -> Path:
    value = os.environ.get(name)
    if value:
        return Path(value).expanduser().resolve()
    return default


# Defaults are the framework paths; the env overrides exist only so the desk
# can be exercised against scratch files without touching live state.
BLOCKERS_PATH = _path_from_env("GOLDBACH_BLOCKERS_FILE", ROOT / "map" / "blockers.json")
STATE_PATH = _path_from_env("GOLDBACH_DESK_STATE", HERE / "state.json")
LEASES_PATH = _path_from_env("GOLDBACH_LEASES_LOG", HERE / "leases.jsonl")


# --------------------------------------------------------------------------
# time helpers


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def iso(moment: datetime) -> str:
    return moment.astimezone(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_iso(value: Any) -> datetime:
    """Parse one of our ISO timestamps; accept both 'Z' and '+00:00'."""
    text = str(value).strip().replace("Z", "+00:00")
    moment = datetime.fromisoformat(text)
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc)


def minutes_left(lease: dict, at: datetime | None = None) -> float:
    at = at or now_utc()
    return (parse_iso(lease["expires"]) - at).total_seconds() / 60.0


# --------------------------------------------------------------------------
# state, lock, event log


def empty_state() -> dict:
    return {"leases": [], "submissions": []}


def load_state() -> dict:
    if not STATE_PATH.exists():
        return empty_state()
    try:
        data = json.loads(STATE_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise DeskError(f"cannot read state file {STATE_PATH}: {exc}") from exc
    if not isinstance(data, dict):
        raise DeskError(f"state file {STATE_PATH} must contain a JSON object")
    for key in ("leases", "submissions"):
        if not isinstance(data.get(key), list):
            data[key] = []
    return data


def save_state(state: dict) -> None:
    STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE_PATH.with_name(f".{STATE_PATH.name}.{os.getpid()}.tmp")
    try:
        tmp.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        os.replace(tmp, STATE_PATH)
    finally:
        if tmp.exists():
            tmp.unlink()


@contextmanager
def desk_lock() -> Iterator[Any]:
    """Serialize read-modify-write cycles; the leases log doubles as the lock file."""
    LEASES_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(LEASES_PATH, "a+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield handle
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def append_event(handle: Any, event: dict) -> None:
    record = {"ts": iso(now_utc())}
    record.update(event)
    handle.write(json.dumps(record, ensure_ascii=False) + "\n")
    handle.flush()


def purge_expired(state: dict, handle: Any) -> None:
    """Drop expired leases from live state and leave an audit trail."""
    kept: list[dict] = []
    for lease in state["leases"]:
        if is_active(lease):
            kept.append(lease)
        else:
            append_event(
                handle,
                {
                    "event": "expire",
                    "lease_id": lease.get("lease_id"),
                    "blocker_id": lease.get("blocker_id"),
                    "holder": lease.get("holder"),
                },
            )
    state["leases"] = kept


# --------------------------------------------------------------------------
# blockers.json (accept a bare list, a {"blockers": [...]} wrapper, or a map)


def load_blockers() -> list[dict]:
    if not BLOCKERS_PATH.exists():
        raise DeskError(
            f"blockers file not found: {BLOCKERS_PATH} — create map/blockers.json first"
        )
    try:
        data = json.loads(BLOCKERS_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise DeskError(f"cannot read blockers file {BLOCKERS_PATH}: {exc}") from exc

    if isinstance(data, list):
        items = data
    elif isinstance(data, dict):
        items = None
        for key in ("blockers", "items", "open"):
            if isinstance(data.get(key), list):
                items = data[key]
                break
        if items is None:
            if data and all(isinstance(v, dict) for v in data.values()):
                items = []
                for key, value in data.items():
                    item = dict(value)
                    item.setdefault("id", key)
                    items.append(item)
            else:
                raise DeskError(
                    f"{BLOCKERS_PATH}: expected a list of blockers or a "
                    "'blockers' list"
                )
    else:
        raise DeskError(f"{BLOCKERS_PATH}: expected a JSON list or object")

    blockers: list[dict] = []
    for index, raw in enumerate(items):
        if not isinstance(raw, dict):
            continue
        blocker = dict(raw)
        identifier = blocker.get("id") or blocker.get("blocker_id") or blocker.get("key")
        blocker["id"] = str(identifier) if identifier else f"blocker-{index + 1:03d}"
        blocker.setdefault("status", "open")
        blockers.append(blocker)
    return blockers


def is_open(blocker: dict) -> bool:
    return str(blocker.get("status", "open")).strip().lower() in ("open", "attackable", "")


def program_of(blocker: dict) -> str:
    value = blocker.get("program") or blocker.get("program_key") or blocker.get("track") or ""
    return str(value).strip().lower()


def difficulty_rank(blocker: dict) -> float:
    value = blocker.get("difficulty", "")
    if isinstance(value, (int, float)):
        return float(value)
    text = str(value).strip().lower()
    ranks = {
        "trivial": 0, "easy": 1, "low": 1, "medium": 2, "moderate": 2,
        "hard": 3, "high": 3, "research": 4, "very hard": 5, "very_hard": 5,
        "extreme": 6,
    }
    if text in ranks:
        return ranks[text]
    try:
        return float(text)
    except ValueError:
        return 2.0  # unknown difficulty: neutral


def parallel_capacity(blocker: dict, holder: str) -> int:
    """How many simultaneous holders blockers.json allows for this blocker.

    Accepts an integer capacity (the form used by map/blockers.json), a list of
    named holders, a boolean, or a wildcard string.  Zero means exclusive.
    """
    spec = blocker.get("parallel", blocker.get("parallel_holders"))
    if spec is None or spec is False:
        return 1
    if isinstance(spec, bool):  # True: no explicit limit
        return 10_000
    if isinstance(spec, int):
        return max(1, spec)
    if isinstance(spec, str):
        text = spec.strip().lower()
        if text in ("true", "yes", "*", "any", "all"):
            return 10_000
        return 10_000 if text == holder.lower() else 1
    if isinstance(spec, (list, tuple, set)):
        allowed = {str(item).lower() for item in spec}
        if not allowed or "*" in allowed or "any" in allowed or holder.lower() in allowed:
            return 10_000
    return 1


# --------------------------------------------------------------------------
# leases


def is_active(lease: dict, at: datetime | None = None) -> bool:
    try:
        return minutes_left(lease, at) > 0
    except (KeyError, ValueError, TypeError):
        return False


def active_leases(state: dict, at: datetime | None = None) -> list[dict]:
    return [lease for lease in state["leases"] if is_active(lease, at)]


def find_lease(state: dict, lease_id: str) -> dict | None:
    for lease in state["leases"]:
        if lease.get("lease_id") == lease_id:
            return lease
    return None


def new_lease(blocker: dict, holder: str) -> dict:
    created = now_utc()
    return {
        "lease_id": uuid.uuid4().hex,
        "blocker_id": blocker["id"],
        "holder": holder,
        "expires": iso(created + timedelta(minutes=LEASE_MINUTES)),
        "beats": 0,
        "max_beats": MAX_BEATS,
        "created": iso(created),
    }


# --------------------------------------------------------------------------
# commands


def cmd_next(args: argparse.Namespace) -> int:
    with desk_lock() as handle:
        state = load_state()
        purge_expired(state, handle)
        blockers = load_blockers()

        active = active_leases(state)
        leased: dict[str, list[dict]] = {}
        for lease in active:
            leased.setdefault(lease["blocker_id"], []).append(lease)
        mine = {lease["blocker_id"] for lease in active if lease.get("holder") == args.holder}

        wanted = args.program.strip().lower() if args.program else None
        only_id = getattr(args, "id", None)
        candidates: list[dict] = []
        for blocker in blockers:
            if not is_open(blocker):
                continue
            if wanted and program_of(blocker) != wanted:
                continue
            if only_id and blocker["id"] != only_id:
                continue
            blocker_id = blocker["id"]
            if blocker_id in mine:
                continue  # do not hand the same holder two leases on one blocker
            others = [l for l in leased.get(blocker_id, []) if l.get("holder") != args.holder]
            if len(others) >= parallel_capacity(blocker, args.holder):
                continue
            candidates.append(blocker)

        if not candidates:
            reason = "no open, unleased blocker"
            if wanted:
                reason += f" for program '{args.program}'"
            save_state(state)
            print(json.dumps({"blocker": None, "lease": None, "reason": reason}, indent=2))
            return 1

        if args.hard:
            candidates.sort(key=difficulty_rank, reverse=True)  # stable: file order on ties
        blocker = candidates[0]
        lease = new_lease(blocker, args.holder)
        state["leases"].append(lease)
        save_state(state)
        append_event(handle, {"event": "lease", "lease": lease})
        print(json.dumps({"blocker": blocker, "lease": lease}, indent=2))
        return 0


def cmd_beat(args: argparse.Namespace) -> int:
    with desk_lock() as handle:
        state = load_state()
        purge_expired(state, handle)
        lease = find_lease(state, args.lease_id)
        if lease is None:
            raise DeskError(f"lease not found or expired: {args.lease_id}")
        maximum = int(lease.get("max_beats", MAX_BEATS))
        if int(lease.get("beats", 0)) >= maximum:
            raise DeskError(f"beat limit reached ({maximum}) for lease {args.lease_id}")
        lease["beats"] = int(lease.get("beats", 0)) + 1
        lease["expires"] = iso(now_utc() + timedelta(minutes=LEASE_MINUTES))
        save_state(state)
        append_event(
            handle,
            {
                "event": "beat",
                "lease_id": lease["lease_id"],
                "beats": lease["beats"],
                "expires": lease["expires"],
            },
        )
        print(
            json.dumps(
                {
                    "lease_id": lease["lease_id"],
                    "beats": lease["beats"],
                    "max_beats": maximum,
                    "expires": lease["expires"],
                },
                indent=2,
            )
        )
        return 0


def cmd_release(args: argparse.Namespace) -> int:
    with desk_lock() as handle:
        state = load_state()
        purge_expired(state, handle)
        lease = find_lease(state, args.lease_id)
        if lease is None:
            raise DeskError(f"lease not found or expired: {args.lease_id}")
        state["leases"] = [l for l in state["leases"] if l["lease_id"] != args.lease_id]
        save_state(state)
        append_event(
            handle,
            {
                "event": "release",
                "lease_id": lease["lease_id"],
                "blocker_id": lease.get("blocker_id"),
                "holder": lease.get("holder"),
                "reason": args.reason,
            },
        )
        print(
            json.dumps(
                {
                    "status": "released",
                    "lease_id": lease["lease_id"],
                    "blocker_id": lease.get("blocker_id"),
                    "reason": args.reason,
                },
                indent=2,
            )
        )
        return 0


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with open(path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as exc:
        raise DeskError(f"cannot read submission file {path}: {exc}") from exc
    return digest.hexdigest()


def cmd_submit(args: argparse.Namespace) -> int:
    path = Path(args.file).expanduser()
    if not path.is_file():
        raise DeskError(f"submission file not found: {path}")
    checksum = sha256_file(path)

    with desk_lock() as handle:
        state = load_state()
        purge_expired(state, handle)
        lease = find_lease(state, args.lease_id)
        if lease is None:
            raise DeskError(f"lease not found or expired: {args.lease_id}")
        submission = {
            "submission_id": uuid.uuid4().hex,
            "lease_id": lease["lease_id"],
            "blocker_id": lease.get("blocker_id"),
            "holder": lease.get("holder"),
            "file": str(path.resolve()),
            "sha256": checksum,
            "created": iso(now_utc()),
        }
        state["submissions"].append(submission)
        state["leases"] = [l for l in state["leases"] if l["lease_id"] != args.lease_id]
        save_state(state)
        append_event(
            handle,
            {
                "event": "release",
                "lease_id": lease["lease_id"],
                "blocker_id": lease.get("blocker_id"),
                "holder": lease.get("holder"),
                "reason": "submitted",
            },
        )
        append_event(handle, {"event": "submit", "submission": submission})
        print(json.dumps({"status": "submitted", "submission": submission}, indent=2))
        return 0


def cmd_status(args: argparse.Namespace) -> int:
    with desk_lock() as handle:
        state = load_state()
        at = now_utc()
        active = active_leases(state, at)
        blockers = load_blockers() if BLOCKERS_PATH.exists() else []
        open_blockers = [blocker for blocker in blockers if is_open(blocker)]
        held_counts: dict[str, int] = {}
        for lease in active:
            held_counts[lease["holder"]] = held_counts.get(lease["holder"], 0) + 1
        expiries = []
        for lease in sorted(active, key=lambda l: l.get("expires", "")):
            try:
                remaining = round(minutes_left(lease, at), 1)
            except (KeyError, ValueError, TypeError):
                remaining = None
            expiries.append(
                {
                    "lease_id": lease.get("lease_id"),
                    "holder": lease.get("holder"),
                    "blocker_id": lease.get("blocker_id"),
                    "expires": lease.get("expires"),
                    "minutes_remaining": remaining,
                }
            )
        print(
            json.dumps(
                {
                    "generated": iso(at),
                    "blockers_file": str(BLOCKERS_PATH),
                    "blockers_found": BLOCKERS_PATH.exists(),
                    "open_count": len(open_blockers),
                    "open_blockers": open_blockers,
                    "active_lease_count": len(active),
                    "active_leases": active,
                    "held_counts": held_counts,
                    "expiries": expiries,
                    "submission_count": len(state["submissions"]),
                },
                indent=2,
            )
        )
        return 0


def cmd_blockers(args: argparse.Namespace) -> int:
    blockers = load_blockers()
    print(json.dumps({"count": len(blockers), "blockers": blockers}, indent=2))
    return 0


# --------------------------------------------------------------------------
# CLI


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Local file-based desk for GOLDBACH ATTACK (leases, not verification)."
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_next = sub.add_parser("next", help="lease the next open blocker")
    p_next.add_argument("--holder", required=True, help="agent name taking the lease")
    p_next.add_argument("--program", help="restrict to a program key (found, cond, sieve, ...)")
    p_next.add_argument("--hard", action="store_true", help="prefer the hardest available blocker")
    p_next.add_argument("--id", help="lease exactly this blocker id (skips ranking)")
    p_next.set_defaults(func=cmd_next)

    p_beat = sub.add_parser("beat", help="renew a lease for another 45 minutes")
    p_beat.add_argument("lease_id")
    p_beat.set_defaults(func=cmd_beat)

    p_release = sub.add_parser("release", help="give a lease back with a reason")
    p_release.add_argument("lease_id")
    p_release.add_argument("reason")
    p_release.set_defaults(func=cmd_release)

    p_submit = sub.add_parser("submit", help="record a submission and release its lease")
    p_submit.add_argument("lease_id")
    p_submit.add_argument("file")
    p_submit.set_defaults(func=cmd_submit)

    p_status = sub.add_parser("status", help="show open blockers, leases, holders and expiries")
    p_status.set_defaults(func=cmd_status)

    p_blockers = sub.add_parser("blockers", help="list every blocker with its status")
    p_blockers.set_defaults(func=cmd_blockers)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except DeskError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("error: interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
