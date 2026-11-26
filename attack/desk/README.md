# desk — local file-based lease desk

`desk/desk.py` hands out work on open blockers using plain JSON/JSONL files.
It is stdlib-only Python 3 and does **not** run the checker or modify
`map/blockers.json`. Its job is to stop two agents attacking the same blocker
and to leave an audit trail of beats, releases and submissions.

## Files

| path | contents |
|---|---|
| `../map/blockers.json` | read-only input, created by the parent (`blockers` list is expected) |
| `state.json` | `{"leases": [...], "submissions": [...]}` — created on first write |
| `leases.jsonl` | append-only event log: `lease`, `beat`, `release`, `submit`, `expire` |

All timestamps are UTC ISO-8601 (`2026-11-26T21:00:00Z`). A lease is
 `{lease_id, blocker_id, holder, expires, beats, max_beats, created}` with a
45 minute expiry and at most 12 beats. An expired lease is automatically treated as
free (and is purged from `state.json` on the next mutating command). Read/write
cycles are serialized with an advisory lock on `leases.jsonl`.

## Commands

```sh
python3 desk/desk.py next --holder alice                 # first open, unleased blocker
python3 desk/desk.py next --holder alice --program found # restrict to program key
python3 desk/desk.py next --holder bob --hard            # hardest available first
python3 desk/desk.py beat <lease_id>                     # +45 min (max 12 beats)
python3 desk/desk.py release <lease_id> "blocked by PARITY"
python3 desk/desk.py submit <lease_id> proof/WeakGoldbach.lean
python3 desk/desk.py status                              # JSON: open, leases, holders, expiries
python3 desk/desk.py blockers                            # JSON: every blocker and its status
```

`next` prints `{"blocker": {...}, "lease": {...}}` so an agent can pick up its
assignment directly. If there is nothing available it prints
`{"blocker": null, "lease": null, "reason": "..."}` and exits 1. If
`map/blockers.json` is missing it prints a clear error and exits 2. `status`
still works (empty lists) when the blockers file is absent.

`--hard` orders candidates by difficulty (`easy` < `medium` < `hard` <
`research`, numeric values allowed), then takes the highest. Ties keep the
order in `blockers.json`.

Parallel work is honoured from blocker metadata: an integer `parallel: N`
allows up to N holders on the same blocker, a list of names allows those
holders, `true`/`*` allows anyone; absent/`false`/`0` means exclusive. One
holder never gets two leases on the same blocker.

`submit` only records the file path and sha256; it releases the lease with
reason `submitted`. **Verification happens separately** with
`checker/check.py file|lean|verifier`, followed by `checker/check.py verdict`.

## Exit codes

`0` success, `1` no blocker available (`next`), `2` user error / missing file.
Every output is JSON on stdout; errors are one `error: ...` line on stderr.

## Testing hooks

The four paths can be overridden by environment variables so the desk can be
exercised without touching live state:
`GOLDBACH_BLOCKERS_FILE`, `GOLDBACH_DESK_STATE`, `GOLDBACH_LEASES_LOG`.
Defaults are the framework paths under `/home/eequaled/goldbach`.
