# Preliminary audit findings (parent, 2026-11-26) — subject to the full audit

Independent quick checks run by the parent while the full audit subagent fetches Mathlib.
Every command below was actually run; outputs are honest.

## 1. Banned-token scan of the Lean sources (`grep -rniE`)

- `sorry`: **4 hits, ALL in comments** (e.g. "zero `sorry`s"). No actual `sorry` term.
- `native_decide`, `unsafe`, `admit`, `opaque`, `implemented_by`: **0 hits**.
- `axiom`: **17 declarations** (the word appears 19 times counting comments). This is the
  critical finding: the README says "sorry-free" (true) but does NOT say "axiom-free".

The 17 declared axioms:

| File | Axioms |
|---|---|
| `WeakGoldbach/Analytic.lean:430-454` | `R_total`, `M_coeff`, `grh_arc_error_bound`, `major_arc_main_term_lower_bound`, `prime_power_subtraction_bound` (5) |
| `WeakGoldbach/BinaryExceptional.lean:33-73` | `R2_total`, `M2_coeff`, `T_trunc`, `U_tail`, `S2_series`, `J_int`, `grh_binary_arc_L2_bound`, `binary_singular_integral_bounds`, `binary_singular_series_bounds`, `binary_prime_power_bound` (10) |
| `WeakGoldbach/Main.lean:15,23` | `binaryGoldbach_4e18` (unproved finite check to 4·10¹⁸), `certified_prime_ladder_1e22` (unproved external ladder to 10²²) (2) |

Consequence: `weak_goldbach_theorem` and `binary_goldbach_exceptional_bound` are **NOT**
unconditional kernel proofs. They are derivations from the above axioms. `#print axioms` sites
exist (`BinaryExceptional.lean:274-275`, `Main.lean:40`) — the full audit should capture their
actual output once the build runs.

Status decision (per AGENTS.md §0): both remain `conditional`, with hypotheses:
- weak: GRH + the five Analytic.lean axioms + the 4·10¹⁸ finite axiom + the ladder axiom
- binary exceptional: GRH + the ten BinaryExceptional.lean axioms + the 4·10¹⁸ axiom

## 2. Python interval verifiers (actually run)

```
python3 verify/verify_bounds.py        -> exit 0; "ALL ANALYTIC CONSTANTS AND INEQUALITIES VERIFIED WITH RIGOROUS INTERVAL BOUNDS!"
python3 verify/verify_binary_bounds.py -> exit 0; "ALL BINARY GOLDBACH EXCEPTIONAL-SET CONSTANTS AND INEQUALITIES VERIFIED!"
```
So the analytic constants are independently checkable — that part of the repo is sound. It does
not discharge the axioms: axioms are assumptions, not numbers.

## 3. Not yet verified

- `lake build` on v4.16.0: NOT run by parent; audit subagent is fetching the Mathlib cache
  (`lake exe cache get`, observed running ~3 min). No success claim until it reports.
- `verify_finite.cpp` compiled/run: NOT by parent. Do not run to 10⁹ (hours).
- `verify_ladder.py`: read-only; not run over the full range.

## Derived rules (add to failures.md after full audit)

1. "sorry-free" ≠ "axiom-free". Always grep `axiom` and capture `#print axioms` output.
2. A theorem built on declared analytic axioms is conditional, even if the Lean kernel checks
   the derivation. Keep its hypothesis in the claim id.
3. Numeric verifier PASS validates constants only — not the assumptions that consume them.
