# Vendored from brilliant-hq/pequalnp-proofs

Source: https://github.com/brilliant-hq/pequalnp-proofs (commit 44d5a85, cloned 2026-11-18).
License: **Apache License 2.0** (NOT MIT — corrected 2026-11-26). Full license in `LICENSE`.

Copied verbatim, with attribution, because the checker is a mature, independently-audited piece
of infrastructure: it re-kernel-checks every declaration a theorem rests on, checks for banned
axioms/sorry/native_decide, and verifies the theorem is exactly the recorded statement. Rebuilding
that from scratch would be wasteful and less trustworthy.

| File | What it is |
|---|---|
| `tools/check-lean.mjs` | THE checker — kernel re-check + axiom audit + exact-statement verification. Exit 0 = accepted. |
| `tools/pnp.sh` | Reference desk script (lease/next/beat/release/submit) — pattern for our `desk/desk.py`. |
| `lean/CheckLemma.lean` | Lean-side verifier used by check-lean.mjs (259 lines). |
| `workflows/advisory.yml`, `workflows/authoritative.yml` | Reference CI checks — pattern for our checker integration. |
| `LICENSE` | Apache 2.0 license text. |

Adaptation for Goldbach: the checker expects a project with `lean/lean-toolchain`,
`lean/lake-manifest.json` and a definitions root. Our Lean tree lives in
`goldbach-grh-lean/lean/` (pinned v4.16.0). Do NOT claim a vendored tool works on our tree until a
run is recorded in `checker/runs.jsonl`. The local `checker/check.py` wraps these commands.
