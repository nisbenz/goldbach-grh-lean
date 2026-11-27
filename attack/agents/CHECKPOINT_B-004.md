# B-004 research checkpoint

- [Q] 2026-11-27 16:20 UTC. Read both open issues and acquired B-004 lease `a7a1eb2ffd0547c5850907b0ffb14376`. B-014 is the companion. Start note posted on #4.
- [I] Plan. Recompute the cutoff envelopes, distinguish the two endpoint weights, and compare symbolic finite arithmetic with controlled numerical enclosures. Proposed Lean work and analytic hypotheses retain their own status.
- [P] Re-derived the three cutoff balances and the balanced-block range. Generated exact log-pair coefficients for 39 targets and Arb enclosures for both endpoint weights. At 8, the narrow PSD test has zero actual mass. The original-weight top conductor has sizeable contributions from other multiples of p in the finite sample.
- [P] Completed the original fixed-weight sum through 5N with a rigorous exponential tail. Both endpoint normalizations and conditional (16) are documented in the audit. Added an elementary comparison for the varying minorant and identified the single-target signed estimate left after exact projection.
- [Q] Final. Both tracked issues and map entries were open on recheck. Released lease `a7a1eb2ffd0547c5850907b0ffb14376` with reason `missing_lemma`. [Closing comment on #4](https://github.com/nisbenz/goldbach-grh-lean/issues/4#issuecomment-7223350692) · [Closing comment on #11](https://github.com/nisbenz/goldbach-grh-lean/issues/11#issuecomment-7223352318).
- [I] Recommend consolidating the analytic estimates under B-004. The proposed dyadic projector specification has research status only. [Full report](/home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B004_B014_GWX_RATIOS_ATTACK.md).

## Wave 3 — Astra (astra-w3-b004)

- [Q] Issue #4 and the local blocker were open at acquisition of lease `890bd50757ca4de0854127dddea787e1`. [Start note](https://github.com/nisbenz/goldbach-grh-lean/issues/4#issuecomment-7224196699)
- [I] Test the linear upper sieve on the prime cofactor, the endpoint of the rough lower sieve, and smooth localization of the subtracted primitive projector.
- [P] The fixed balanced test lies strictly below the product cutoff. At an odd prime-square conductor the finer grid costs only square-root order after normalization under Dirichlet GRH. The surviving line is the fixed-target shifted convolution.
- [P] The fixed-factor upper coefficient is 4. The product sieve narrows to 1.899956 or, under WEH(0.999), 1.393854 given the respective [U] supplies. The rough endpoint buys 81.706% unsigned baseline. The scan checked both marks numerically for all 99,999 even targets through 200,000. [Report](../audit/B004_B015_W3_PERSISTENT_THRESHOLD_PUSH.md)
- [Q] Released lease `890bd50757ca4de0854127dddea787e1` with `missing_lemma`. [Issue #4](https://github.com/nisbenz/goldbach-grh-lean/issues/4#issuecomment-7224353600) · [Issue #12](https://github.com/nisbenz/goldbach-grh-lean/issues/12#issuecomment-7224353996) · [Issue #5](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7224354448)
