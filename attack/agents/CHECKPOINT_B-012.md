# B-012 · astra-b012 · 2026-11-27

- [P] Read the issue and research handoff, confirmed the blocker is open, and acquired lease c84b419d1b1f4cc88ea8f6dcd98aaf50. [Start comment](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7223154368)
- [I] Compare rough mass, ordered factorizations and the signed quadratic form on five targets. Check the role of the coprimality mask and reflected prime powers explicitly.
- [U] A target-uniform bound for the genuine coefficients remains to be established.
- [P] All five targets ran. Independent Eratosthenes sieving reproduced the genuine rough mass, prime mass and ordered rough pair count on all five. The signed off-diagonal is negative for the genuine rows and positive for both models in the selected boxes.
- [P] For powers of two, projecting the model's centered column sums onto Liouville yields an order-N projection and an order-N^(3/2) lower bound for its quadratic form by Cauchy–Schwarz and the classical prime number theorem. The detailed derivation is in the audit.
- [P] Completed the audit, literature comparisons and proposed weighted Lean declarations. Reproducing the program gave byte-identical JSON. The appendix contains the exact program.
- [U] Missing estimate: a target-uniform upper bound for the genuine signed two-form term, or a direct rough estimate S−B>2E with E the reflected higher-power contribution. The proposed Lean declarations have no strict-check verdict.
- [P] Desk release confirmed for c84b419d1b1f4cc88ea8f6dcd98aaf50 with reason missing_lemma. Posted the [closing findings](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7223316597). [Audit](../audit/B012_BILINEAR_PARITY_ATTACK.md)
