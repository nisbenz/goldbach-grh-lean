#!/usr/bin/env python3
"""Local proof checker for the GOLDBACH ATTACK framework.

Commands: file, lean, verifier, verdict.

Verdicts are deliberately honest:
  ACCEPTED - command exited 0 (or a format check passed)
  REJECTED - command ran and reported a failure (nonzero exit / format violation)
  FAULT    - the check could not run at all: missing script, missing toolchain,
             timeout, bad cwd, ... A FAULT is never evidence against a proof.

Every run is appended to checker/runs.jsonl.  The desk does not call this
program; the parent re-verifies every submission here.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import shlex
import subprocess
import sys
import uuid
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterator

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

LEAN_TIMEOUT = 20 * 60       # seconds
VERIFIER_TIMEOUT = 10 * 60   # seconds
TAIL_LINES = 20
BANNED_TOKENS = ("sorry", "axiom", "native_decide", "unsafe", "admit")
BANNED_RE = re.compile(r"\b(" + "|".join(BANNED_TOKENS) + r")\b")

# Infrastructure failures must never be recorded as a rejection of a proof.
TOOLCHAIN_FAULT_RE = re.compile(
    r"no default toolchain configured|"
    r"(?:unknown|no such|missing) toolchain|"
    r"toolchain .*(?:not installed|is not installed)|"
    r"could not canonicalize path|"
    r"command not found",
    re.IGNORECASE,
)
IMPORT_FAULT_RE = re.compile(r"ModuleNotFoundError|ImportError: No module named", re.IGNORECASE)


class CheckError(Exception):
    """A user-facing error (printed as 'error: ...', no traceback)."""


def _path_from_env(name: str, default: Path) -> Path:
    value = os.environ.get(name)
    if value:
        return Path(value).expanduser().resolve()
    return default


# Env override exists only for isolated testing; default is the framework log.
RUNS_PATH = _path_from_env("GOLDBACH_RUNS_LOG", HERE / "runs.jsonl")


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def iso(moment: datetime) -> str:
    return moment.astimezone(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


# --------------------------------------------------------------------------
# append-only run log


@contextmanager
def runs_lock() -> Iterator[Any]:
    RUNS_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(RUNS_PATH, "a+", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield handle
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def append_run(record: dict) -> None:
    with runs_lock() as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + "\n")
        handle.flush()


def load_runs() -> list[dict]:
    if not RUNS_PATH.exists():
        return []
    records: list[dict] = []
    for line in RUNS_PATH.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except ValueError:
            continue  # tolerate a truncated last line
        if isinstance(value, dict):
            records.append(value)
    return records


def make_record(kind: str, command: str, cwd: Path, started: datetime) -> dict:
    return {
        "run_id": uuid.uuid4().hex,
        "kind": kind,
        "command": command,
        "cwd": str(cwd),
        "exit": None,
        "started": iso(started),
        "ended": iso(started),
        "output_tail": "",
        "verdict": "FAULT",
    }


def finish_and_emit(record: dict, started: datetime, output: str, exit_code: int | None,
                    verdict: str, reason: str | None = None) -> int:
    record["ended"] = iso(now_utc())
    record["exit"] = exit_code
    record["output_tail"] = "\n".join((output or "").splitlines()[-TAIL_LINES:])
    record["verdict"] = verdict
    if reason:
        record["reason"] = reason
    append_run(record)
    emit(record)
    return {"ACCEPTED": 0, "REJECTED": 1, "FAULT": 2}[verdict]


def emit(record: dict) -> None:
    print(
        f"{record['verdict']} run_id={record['run_id']} "
        f"kind={record['kind']} exit={record['exit']}"
    )
    if record.get("reason"):
        print(f"reason: {record['reason']}")
    # The file command already printed its own PASS/FAIL lines; don't echo them.
    if record.get("output_tail") and record["kind"] != "file":
        print(record["output_tail"])


def fault(kind: str, command: str, cwd: Path, reason: str) -> int:
    started = now_utc()
    record = make_record(kind, command, cwd, started)
    return finish_and_emit(record, started, "", None, "FAULT", reason)


# --------------------------------------------------------------------------
# format checks


def strip_lean_comments(text: str) -> str:
    """Remove -- line comments and (possibly nested) /- -/ block comments.

    Newlines are preserved so reported line numbers stay correct.
    """
    out: list[str] = []
    index = 0
    length = len(text)
    depth = 0
    while index < length:
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            elif text[index] == "\n":
                out.append("\n")
                index += 1
            else:
                index += 1
        elif text.startswith("--", index):
            while index < length and text[index] != "\n":
                index += 1
        elif text.startswith("/-", index):
            depth += 1
            index += 2
        else:
            out.append(text[index])
            index += 1
    return "".join(out)


def check_format(path: Path) -> tuple[bool, list[str]]:
    """Return (passed, reasons).  Lean-specific rules apply to *.lean files."""
    reasons: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return False, [f"cannot read file as UTF-8 text: {exc}"]

    is_lean = path.suffix == ".lean"
    scan = strip_lean_comments(text) if is_lean else text

    for match in BANNED_RE.finditer(scan):
        line = scan.count("\n", 0, match.start()) + 1
        reasons.append(f"line {line}: forbidden token '{match.group(1)}'")

    if is_lean:
        quote = scan.find('"')
        if quote >= 0:
            reasons.append(f"line {scan.count(chr(10), 0, quote) + 1}: double quote is forbidden")
        lines = scan.splitlines()
        for line_no, line in enumerate(lines, 1):
            if line.lstrip().startswith("#"):
                reasons.append(f"line {line_no}: Lean '#' command is forbidden")
        seen_non_import = False
        for line_no, line in enumerate(lines, 1):
            stripped = line.strip()
            if not stripped:
                continue
            if re.match(r"^import(\s|$)", stripped):
                if seen_non_import:
                    reasons.append(f"line {line_no}: import after non-import line")
                continue
            seen_non_import = True

    return not reasons, reasons


def cmd_file(args: argparse.Namespace) -> int:
    path = Path(args.path).expanduser()
    started = now_utc()
    cwd = Path.cwd()
    record = make_record("file", shlex.join(["file", str(path)]), cwd, started)

    if not path.exists():
        return fault("file", record["command"], cwd, f"file not found: {path}")
    if not path.is_file():
        return fault("file", record["command"], cwd, f"not a regular file: {path}")

    passed, reasons = check_format(path)
    output_lines = [f"{'PASS' if passed else 'FAIL'} {path}"]
    output_lines += [f"  - {reason}" for reason in reasons[:50]]
    if len(reasons) > 50:
        output_lines.append(f"  ... and {len(reasons) - 50} more reason(s)")

    for line in output_lines:
        print(line)
    return finish_and_emit(
        record,
        started,
        "\n".join(output_lines),
        0 if passed else 1,
        "ACCEPTED" if passed else "REJECTED",
        None if passed else f"{len(reasons)} format violation(s)",
    )


# --------------------------------------------------------------------------
# command runs (lean / verifier)


def build_env() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.is_dir():
        env["PATH"] = str(elan_bin) + os.pathsep + env.get("PATH", "")
    return env


def run_process(kind: str, argv: list[str], cwd: Path, timeout: int, note: str | None) -> int:
    started = now_utc()
    command = shlex.join(argv)
    record = make_record(kind, command, cwd, started)

    if not cwd.is_dir():
        return fault(kind, command, cwd, f"cwd does not exist: {cwd}")

    try:
        completed = subprocess.run(
            argv,
            cwd=str(cwd),
            env=build_env(),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        output = exc.output or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", "replace")
        return finish_and_emit(
            record, started, output, None, "FAULT", f"timeout after {timeout}s"
        )
    except (OSError, ValueError) as exc:
        return fault(kind, command, cwd, f"cannot execute command: {exc}")

    output = completed.stdout or ""
    exit_code = completed.returncode
    if exit_code == 0:
        return finish_and_emit(record, started, output, exit_code, "ACCEPTED", note)

    infrastructure = None
    if kind == "lean":
        match = TOOLCHAIN_FAULT_RE.search(output)
        if match:
            infrastructure = f"Lean toolchain unavailable: {match.group(0)}"
    elif kind == "verifier":
        match = IMPORT_FAULT_RE.search(output)
        if match:
            infrastructure = f"verifier dependency unavailable: {match.group(0)}"
    if infrastructure:
        return finish_and_emit(record, started, output, exit_code, "FAULT", infrastructure)
    return finish_and_emit(
        record, started, output, exit_code, "REJECTED", f"command exited {exit_code}"
    )


def cmd_lean(args: argparse.Namespace) -> int:
    cwd = Path(args.cwd).expanduser().resolve() if args.cwd else Path.cwd()
    note = "lake build exited 0; run 'check.py file <path>' for the token/axiom audit"
    return run_process("lean", ["lake", "build", args.module], cwd, LEAN_TIMEOUT, note)


def cmd_verifier(args: argparse.Namespace) -> int:
    script = Path(args.script).expanduser().resolve()
    argv = [sys.executable, str(script)] + list(args.args)
    command = shlex.join(argv)
    if not script.is_file():
        return fault("verifier", command, Path.cwd(), f"verifier script not found: {script}")
    return run_process("verifier", argv, Path.cwd(), VERIFIER_TIMEOUT, None)


def cmd_verdict(args: argparse.Namespace) -> int:
    runs = load_runs()
    matches = [run for run in runs if run.get("run_id", "").startswith(args.run_id)]
    if not matches:
        raise CheckError(f"no run found with id (or prefix) {args.run_id!r} in {RUNS_PATH}")
    if len(matches) > 1:
        raise CheckError(f"ambiguous run id prefix {args.run_id!r}: {len(matches)} matches")
    print(json.dumps(matches[0], indent=2, ensure_ascii=False))
    return 0


# --------------------------------------------------------------------------
# CLI


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Local proof checker / audit log for GOLDBACH ATTACK."
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_file = sub.add_parser("file", help="format checks on a file")
    p_file.add_argument("path")
    p_file.set_defaults(func=cmd_file)

    p_lean = sub.add_parser("lean", help="run 'lake build <module>'")
    p_lean.add_argument("module")
    p_lean.add_argument("--cwd", help="directory containing lakefile.toml (default: cwd)")
    p_lean.set_defaults(func=cmd_lean)

    p_verifier = sub.add_parser("verifier", help="run a Python verifier script")
    p_verifier.add_argument("script")
    p_verifier.add_argument("args", nargs=argparse.REMAINDER, help="arguments for the script")
    p_verifier.set_defaults(func=cmd_verifier)

    p_verdict = sub.add_parser("verdict", help="print a logged run by id (prefix ok)")
    p_verdict.add_argument("run_id")
    p_verdict.set_defaults(func=cmd_verdict)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except CheckError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("error: interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
