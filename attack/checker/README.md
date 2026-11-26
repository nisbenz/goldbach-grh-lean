# checker — local proof checker and run log

`checker/check.py` is stdlib-only Python 3. It checks submitted files, runs
Lean builds and independent Python verifiers, and records every run in an
append-only JSONL log. It never claims a result the underlying command did not
produce.

## Verdicts

- `ACCEPTED` — command exited 0 (or format check passed). For `lean` this means
  only "lake build exited 0"; run `file` too for the token/axiom audit.
- `REJECTED` — command ran and failed (nonzero exit or format violation).
- `FAULT` — the check could not run: missing script, missing toolchain (also
  detected from `lake`/elan error output), missing Python dependency, timeout,
  bad cwd, etc. A FAULT is **not** evidence against a proof or a claim.

Exit codes: `0` ACCEPTED, `1` REJECTED, `2` FAULT / usage error.

## Commands

```sh
# 1. cheap local format check (PASS/FAIL + reasons)
python3 checker/check.py file goldbach-grh-lean/lean/WeakGoldbach.lean

# 2. kernel check of a Lean module; lake is found via ~/.elan/bin on PATH
python3 checker/check.py lean WeakGoldbach \
    --cwd /home/eequaled/goldbach/goldbach-grh-lean/lean

# 3. independent verifier (any args after the script go to the script)
python3 checker/check.py verifier goldbach-grh-lean/verify/verify_bounds.py --help

# 4. replay a logged run by full id or unique prefix
python3 checker/check.py verdict 29232622dcd14735a7d1f4108e551bf2
```

`file` rejects `sorry`, `axiom`, `native_decide`, `unsafe` and `admit` (word
matches, Lean comments stripped first). For `*.lean` files it additionally
rejects double quotes, line-initial `#` commands (`#check`, `#eval`, ...) and
`import` statements after the first non-import line. Scans are conservative:
a forbidden token in a Python string or comment also counts.

`lean` runs `lake build <module>` with a 20 minute timeout. `verifier` runs
`python3 <script> [args...]` with a 10 minute timeout. Both capture combined
stdout/stderr and record the **last 20 lines** in the log.

## Log format

`checker/runs.jsonl` (created on first run), one JSON object per line:

```json
{"run_id": "<uuid4 hex>", "kind": "lean|verifier|file", "command": "...",
 "cwd": "...", "exit": 0, "started": "...Z", "ended": "...Z",
 "output_tail": "<last 20 lines>", "verdict": "ACCEPTED", "reason": "..."}
```

`verdict <run_id>` prints that object pretty-printed. Set `GOLDBACH_RUNS_LOG`
to redirect the log for isolated testing.

## Honesty rules

1. A passing `lake build` does not by itself mean "no sorry / allowed axioms only":
   run `file` on the relevant sources and record both runs.
2. Timeout, missing `lake`, missing verifier or bad cwd produce `FAULT`, never
   `REJECTED`. Do not turn a FAULT into a claim either way.
3. Every submission from `desk` must be re-verified here by the parent before
   it is marked `checked` in `map/claims.json`.
