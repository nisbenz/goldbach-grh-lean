# B-005 research checkpoint

## Wave 4 — Astra (astra-w4-decisive-sieve)

[Q] B-005, B-012 and B-015 were open at intake. B-005 lease `13a9816177af44b8ad6b2cb19cfa730e` was taken on 2026-11-27 at 17:28 UTC. [Start note](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7224454203)

[I] Derive the dimension-one and switched product coefficients separately, examine their endpoint analytically, and isolate a quantified signed comparison estimate. [U] Pointwise positivity remains open.

[P] The endpoint is exactly minus twice the normalized three-factor simplex integral. The numerical replay now uses two independently discretized interval enclosures. [P] A Ford–Maynard comparison sieve gives an explicit sufficient balanced band, and a three-factor construction bounds the possible optimal endpoint from above. [U] The necessary signed comparison estimate for the genuine shifted primes is outstanding.

[P] Completed the [Wave 4 report](../audit/B005_B012_W4_DECISIVE_PARITY_PHASE_DIAGRAM.md). The explicit minorant is positive for a smaller-factor band starting at exponent 0.4383. The abstract three-factor obstruction takes effect at 0.4756020343943107203… for a guaranteed positive proportion. The 200-bit replay passed, including independent mesh checks and a separate parametrization of the triple integral. [Replay](/tmp/astra_w4_sieve/phase.py)

[Q] B-005 lease released as `missing_lemma`. B-005, B-012 and B-015 were open on the final status check. [B-005 closing comment](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7224764885) · [B-012 cross-note](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7224767113) · [B-015 cross-note](https://github.com/nisbenz/goldbach-grh-lean/issues/12#issuecomment-7224767471)

## Wave 6 — integer transfer of polynomial Goldbach

[Q] B-005 was open at intake. Lease `007c17818d5b482f9b0072f9a1b069d4` began at 19:00 UTC on 27 November 2026. [Start note](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7226088059)

[I] Track the two divisor switches, the sign and endpoints of the integer remainder, and the target-uniform hypotheses behind any positivity conclusion.

[P] Derived the strict reflection endpoint and both affine forms with determinant \(+N\). The raw and centered logarithms give the same full coefficient when \(N-x>1\). The scratch replay compared 586 exact coefficient dictionaries, including both Möbius switches and the strict hyperbola boundary. [Replay](/tmp/astra_w6_2a/check.py)

[P] Completed the [Wave 6 report](../audit/B005_W6_FUNCTION_FIELD_TRANSFER_STRIKE.md). The short part supplies the full singular series under BV at its own cutoff. On a central interval a BV second-moment argument gives typical factor occupancy and positive squarefree mass for the quotient, averaged over the indicated cofactors. Equation (5) gives a one-sided aggregate target, and equation (9) gives a stronger sufficient affine estimate with determinant equal to the even target.

[U] No target-uniform signed estimate for the integer long-divisor tail was established. [Q] Lease released as `missing_lemma`; issue #5 remains open. [Closing note](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7226228850)
