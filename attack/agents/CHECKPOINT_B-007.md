# B-007 verification checkpoint

- [I] astra-w2-b007 holds lease 2ca0253c4f5144078ca56f13f380c489. Issue #6 was open at acquisition.
- [I] Auditing the native verifiers, timing small runs with a hard timeout, and testing a Lean 4.16 scratch certificate. Full-range verification remains outstanding.
- [P] Native source build, M=L=50,000,000, covered 24,999,999 evens in 0.091652351 s with max minimal prime 1,039. Replayed both JSON copies, 2,501 rungs and 86,507 certificate node visits in 0.922122976 s.
- [P] Scratch Lean 4.16 accepted the exact imported BinaryGoldbachUpTo 2000 in 9.591241861 s with the three allowed axioms. Measuring the baseline and improving certificate checking.
- [P] The product-based packed certificate now passes through 10,000 in 5.541009244 s on Lean 4.16. A second kernel replay on a Mathlib-only base checked the project declarations and exact type in 5.391520206 s. Both theorem audits returned exactly propext, Classical.choice and Quot.sound.
- [P] The C++ inputs M=6, L=99 produce a false first-rung bound via unsigned wrap. The separate CPU and Radeon pilot agreed on a four-million-even high slice ending at 10^14. One GPU attempt exited by signal 11, and synchronized repeats passed. Writing the audit and resource model.
- [P] Final sources embedded in the [audit](../audit/B007_COMPUTATIONAL_VERIFICATION_AUDIT.md). The final 10,000-specific build took 5.508629926 s and exact-type replay took 5.380948840 s. The corrupt first witness was rejected. The vendored wrapper in scratch separately returned REJECTED (not-a-project-module).
- [P] The desk released lease 2ca0253c4f5144078ca56f13f380c489 with positional reason other. [U] The external 4 × 10¹⁸ binary premise has no full independent run here. [P] Findings were posted on [issue #6](https://github.com/nisbenz/goldbach-grh-lean/issues/6#issuecomment-7223829728). The blocker and issue remain open.

## Wave 3 — Astra (astra-w3-eng)

- [P] Acquired lease 55cf8dedab64414e8b97d1c6084e638e on open issue #6. [I] Testing the verifier boundaries, paged certificate and Pratt rung costs.
- [P] Fixed the verifier wrap and validated 17 CLI cases. With M=8 the ladder starts at 3 and cannot cross 23→29. (8,27) and (12,99) pass. 
- [P] Exact BinaryGoldbachUpTo 50000 passed a Lean 4.16.0 build and independent kernel replay with only the three allowed axioms. The vendored wrapper rejected the scratch module layout. First five stored Pratt roots passed kernel replay in 1.481904853 s excluding imports.
- [P] Released lease 55cf8dedab64414e8b97d1c6084e638e with reason other. [U] The full binary premise and Lean ladder remain open. [Wave 3 report](../audit/B007_W3_FIX_AND_SCALING.md) · [Issue update](https://github.com/nisbenz/goldbach-grh-lean/issues/6#issuecomment-7224284378)
