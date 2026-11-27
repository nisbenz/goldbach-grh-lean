# B-012 · astra-b012 · 2026-11-27

- [P] Read the issue and research handoff, confirmed the blocker is open, and acquired lease c84b419d1b1f4cc88ea8f6dcd98aaf50. [Start comment](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7223154368)
- [I] Compare rough mass, ordered factorizations and the signed quadratic form on five targets. Check the role of the coprimality mask and reflected prime powers explicitly.
- [U] A target-uniform bound for the genuine coefficients remains to be established.
- [P] All five targets ran. Independent Eratosthenes sieving reproduced the genuine rough mass, prime mass and ordered rough pair count on all five. The signed off-diagonal is negative for the genuine rows and positive for both models in the selected boxes.
- [P] For powers of two, projecting the model's centered column sums onto Liouville yields an order-N projection and an order-N^(3/2) lower bound for its quadratic form by Cauchy–Schwarz and the classical prime number theorem. The detailed derivation is in the audit.
- [P] Completed the audit, literature comparisons and proposed weighted Lean declarations. Reproducing the program gave byte-identical JSON. The appendix contains the exact program.
- [U] Missing estimate: a target-uniform upper bound for the genuine signed two-form term, or a direct rough estimate S−B>2E with E the reflected higher-power contribution. The proposed Lean declarations have no strict-check verdict.
- [P] Desk release confirmed for c84b419d1b1f4cc88ea8f6dcd98aaf50 with reason missing_lemma. Posted the [closing findings](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7223316597). [Audit](../audit/B012_BILINEAR_PARITY_ATTACK.md)

## Wave 5 Strike 1A · 2026-11-27

- [P] Acquired B-012 lease `fbbbf50e7ce64616ab3dcd038d3b984b` and read the Wave 4 coefficient and the two cached preprints. [Start comment](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7225226680)
- [P] Lichtman’s first-3k-hits partition puts every genuine semiprime in the exceptional set for k ≥ 1. [U] Testing the off-diagonal that remains after Cauchy–Schwarz and the one-sided coefficient available from prime EH.
- [P] Resumed with active lease `ed52bf1bfa2d4d15b1990f32c0561923`. Identified the distinction between the Wave 4 smaller-prime count and the three-von-Mangoldt sum. Deriving the transfer by nested rough cutoffs, and testing the exact Selberg quadratic form on a single prime row as well as the genuine Cauchy–Schwarz moment.
- [P, conditional on prime EH] Derived the weighted central-band lower inequality and optimized the prime-row Selberg square. Its infimum coefficient is 2. On any unbounded sequence of Goldbach exceptions the literal triple-weighted ratio would tend to 2. [P] Verified the finite Selberg diagonalization with rationals and the direct Cauchy identity with 128-bit Arb. [U] A normalized off-diagonal below 4 for the genuine prime moment is missing. [Audit](../audit/B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)
- [P] Desk confirmed release of `ed52bf1bfa2d4d15b1990f32c0561923` with reason `missing_lemma`. Posted closing findings on [#9](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7225514096), [#5](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7225514449) and [#12](https://github.com/nisbenz/goldbach-grh-lean/issues/12#issuecomment-7225514900).
