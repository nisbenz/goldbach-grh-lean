# B-005 research checkpoint

## Wave 4 — Astra (astra-w4-decisive-sieve)

[Q] B-005, B-012 and B-015 were open at intake. B-005 lease `13a9816177af44b8ad6b2cb19cfa730e` was taken on 2026-11-27 at 17:28 UTC. [Start note](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7224454203)

[I] Derive the dimension-one and switched product coefficients separately, examine their endpoint analytically, and isolate a quantified signed comparison estimate. [U] Pointwise positivity remains open.

[P] The endpoint is exactly minus twice the normalized three-factor simplex integral. The numerical replay now uses two independently discretized interval enclosures. [P] A Ford–Maynard comparison sieve gives an explicit sufficient balanced band, and a three-factor construction bounds the possible optimal endpoint from above. [U] The necessary signed comparison estimate for the genuine shifted primes is outstanding.

[P] Completed the [Wave 4 report](../audit/B005_B012_W4_DECISIVE_PARITY_PHASE_DIAGRAM.md). The explicit minorant is positive for a smaller-factor band starting at exponent 0.4383. The abstract three-factor obstruction takes effect at 0.4756020343943107203… for a guaranteed positive proportion. The 200-bit replay passed, including independent mesh checks and a separate parametrization of the triple integral. [Replay](/tmp/astra_w4_sieve/phase.py)

[Q] B-005 lease released as `missing_lemma`. B-005, B-012 and B-015 were open on the final status check. [B-005 closing comment](https://github.com/nisbenz/goldbach-grh-lean/issues/5#issuecomment-7224764885) · [B-012 cross-note](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7224767113) · [B-015 cross-note](https://github.com/nisbenz/goldbach-grh-lean/issues/12#issuecomment-7224767471)
