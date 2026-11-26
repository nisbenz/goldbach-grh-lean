#!/usr/bin/env python3
"""Strict checker wrapper — uses the VENDORED Apache-2.0 pequalnp checker.

This is the real check: kernel re-check of every declaration, banned-axiom audit, and exact
statement match. The local checker/check.py handles quick format checks; this wrapper runs the
vendored tools/check-lean.mjs against a submitted Lean file + statement file.

Attribution: brilliant-hq/pequalnp-proofs, Apache 2.0 (see vendor/pequalnp/README.md + LICENSE).
Do NOT modify the vendored checker — adapt inputs around it instead.

Usage:
  python3 checker/strict_check.py <lean_file> <statement_file> [check|refute]
"""
import argparse, os, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CHECKER = ROOT / "vendor/pequalnp/tools/check-lean.mjs"
RUNS = ROOT / "checker/runs.jsonl"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("lean_file")
    ap.add_argument("statement_file")
    ap.add_argument("kind", nargs="?", default="check", choices=["check", "refute"])
    a = ap.parse_args()

    if not CHECKER.exists():
        print(f"FAULT: vendored checker missing: {CHECKER}"); return 2
    if not pathlib.Path(a.lean_file).exists():
        print(f"FAULT: lean file missing: {a.lean_file}"); return 2
    if not pathlib.Path(a.statement_file).exists():
        print(f"FAULT: statement file missing: {a.statement_file}"); return 2

    env = os.environ.copy()
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    cmd = ["node", str(CHECKER), a.lean_file, a.statement_file, a.kind]
    print("RUN:", " ".join(cmd))
    r = subprocess.run(cmd, cwd=str(ROOT), env=env, capture_output=True, text=True, timeout=1800)
    out = (r.stdout or "") + (r.stderr or "")
    verdict = "ACCEPTED" if r.returncode == 0 else ("REJECTED" if r.returncode == 1 else "FAULT")
    print(out[-4000:])
    print(f"STRICT VERDICT: {verdict} (exit {r.returncode}; vendored check-lean.mjs, Apache 2.0)")
    with RUNS.open("a") as f:
        import json, uuid, datetime
        f.write(json.dumps({
            "run_id": uuid.uuid4().hex, "kind": "strict_" + a.kind,
            "command": " ".join(cmd), "cwd": str(ROOT), "exit": r.returncode,
            "verdict": verdict, "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "output_tail": out[-3000:],
        }) + "\n")
    return 0 if verdict == "ACCEPTED" else (1 if verdict == "REJECTED" else 2)

if __name__ == "__main__":
    sys.exit(main())
