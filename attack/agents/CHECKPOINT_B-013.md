# B-013 research checkpoint

[I] astra-b013 read the open issue and leased B-013 under e7704afdb503467ab905068ddd56bfbf. The start note is on issue #10 (comment 7223149874).

[I] Work in progress covers the additive union bound, exact fiber and signed-energy identities, finite prime comparisons and a proposed Lean statement. The research output goes in attack/audit/B013_REFLECTION_HOLE_ATTACK.md.

[I] All seven additive moduli and all sixteen unit-group moduli passed the Python assertions. Exact integer/rational checks cover the cancellation, fiber masses and top signed energies. Independent complex sums cover the spectra. The proof now includes a sharper sine-variance bound and explicit separate even/odd energies for the two families.

[I] A finite Lean declaration on U16 elaborated using the available v4.16.0 toolchain in scratch space. Recording the final declaration, dependencies, genuine-prime comparisons and remaining signed estimate in the audit.

[I] Completed [the research audit](../audit/B013_REFLECTION_HOLE_ATTACK.md), including exact energy formulas, the prime-fiber surplus test and its sieve limitation, and the source code for the reproducible tests. Recorded the failed surplus criterion in [the failure log](../failures.md). The final Lean compilation and dependency printout exited 0.

[U] The all-moduli result still needs strict formal verification. The prime-specific signed inequality still lacks a uniform lower bound. [I] The desk released e7704afdb503467ab905068ddd56bfbf with reason missing_lemma, using the positional reason accepted by this checkout. The issue remained open at handoff. [Closing comment](https://github.com/nisbenz/goldbach-grh-lean/issues/10#issuecomment-7223323772)
