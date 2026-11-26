# MANDATORY agent instructions (Goldbach Attack)

Read ARCHITECTURE.md and failures.md before starting any task.

## Hard rules for every agent
1. Use the `desk`: `python3 desk/desk.py next --holder <your-name> [--program key]` to take a
   blocker. Renew with `beat` every 30 min (45 min lease, 12 beats max). Release when done with
   an honest reason. Submit via `desk.py submit <lease> <file>` — the checker runs separately.
2. Work read-only on git unless the task explicitly says otherwise. NEVER open a PR or push to
   any remote. All state is local.
3. If you prove something: the theorem must be stated EXACTLY as in the claim/blocker, with no
   `sorry`, `axiom`, `native_decide`, `unsafe`, `admit`, `opaque`, `implemented_by`. Lean files:
   imports only at top, no double quotes, no `#` commands beyond `#print axioms` where allowed.
4. MANDATORY self-verification before claiming success: run the relevant check command and paste
   the output. A green build with no theorem is a failure (lesson from the PvNP track).
5. If stuck, report the exact obstacle, what you tried, and any verified partial result. Honest
   partials are useful; fabricated success is logged as a failure.
6. Write a checkpoint file as you go: `/home/eequaled/goldbach/agents/CHECKPOINT_<blocker-id>.md`
   with plan, progress, obstacles. If silent with no writes, the parent will stop and reprompt.
7. If the blocker leaves `open` status in `map/blockers.json` or is resolved elsewhere, STOP and
   report — do not keep working on a dead task.

## Checker commands
- `python3 checker/check.py file <path>` (format)
- `python3 checker/check.py lean <module> [--cwd refs/goldbach-grh-lean/lean]` (kernel build)
- `python3 checker/check.py verifier <script> [args...]` (Python/C++ verifier)

## Honesty
Conditional ≠ unconditional. Finite verification ≠ proof for all n. Literature claim ≠ checked
by us. Every claim carries its status and evidence; failures.md records every mistake with the
rule derived from it.
