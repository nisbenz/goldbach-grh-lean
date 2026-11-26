# GOLDBACH ATTACK — failure log

Started 2026-11-26 on pivot from chess/P-vNP. Inherit the standing rules from the previous track:
log every failure with root cause + derived rule; never claim unverified results; parent re-verifies
subagent output; no PRs/pushes; conditional results keep their hypothesis.

(no failures yet)

### 2026-11-26 — audit finding: "sorry-free" ≠ "axiom-free"
- `grep -rniE` found 17 `axiom` declarations in the cloned Lean sources (5 in Analytic.lean,
  10 in BinaryExceptional.lean, 2 in Main.lean) but only comment-level `sorry` hits. The README
  says "sorry-free", which is true but misleading: the theorems are derived from axioms, so they
  are conditional, not checked. Rule: always grep `axiom` AND capture `#print axioms`; never
  promote a theorem to `checked` on a green build alone. Numeric verifier PASS validates
  constants, not assumptions.

### 2026-11-26 — Mathlib cache host stalled (audit)
- `lake exe cache get` on Lean v4.16.0 timed out twice (300 s, 90 s), exit 124; mathlib cache host
  unresolvable, so `lake build` of the cloned repo could not run. Rule: when a pin's cache is
  unreachable, do NOT report Lean claims as verified; our own clean project uses v4.36.0 with the
  pinned Mathlib rev already cached locally. Keep the unverified label until a build passes.

### 2026-11-27 — desk --hard mis-targets; finite build killed by restarts
- `desk.py next --hard` ranked "research" above "hard", so agents targeting B-003/B-010/B-011 got
  B-012/B-004. Rule: when delegating a specific blocker, add `--id <id>` (now implemented and
  tested) rather than relying on `--hard`. Agents correctly released wrong leases.
- `Finite50000.lean` (2.58 MB, 25k witnesses) generated twice but its `lake build` was killed by
  two server restarts; no `.olean` produced. Discarded — never keep an unverified artifact that
  could be mistaken for a checked result. Keep the checked up-to-10000 certificate instead.
