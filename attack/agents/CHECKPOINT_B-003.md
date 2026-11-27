# CHECKPOINT — B-003 (parity obstruction to level < 1)

## Status: ANALYSIS COMPLETE — no proof, no status change claimed

- Corrected lease obtained with the new `--id` flag:
  `python3 desk/desk.py next --holder agent-b003 --id B-003`
  → lease id `4661f464d04948ccba5ce67fe42e42d0`, blocker **B-003** (confirmed returned),
  created 2026-11-26T22:37:46Z, expires 23:22:46Z. Earlier B-012 lease was released
  before any work (see prior checkpoint entry); desk was fixed by parent with `--id`.
- Renewal: not required — total working time well under 30 minutes.

## Work done

1. Read `AGENTS.md`, `ARCHITECTURE.md`, `audit/REPO_AUDIT.md` (binding context).
2. Quoted the exact construction [Q] from `goldbach-grh-lean/proof/strong_goldbach_research.md`
   lines 120–172 and `strong_goldbach_erh_attack.md` lines 97–103, 128–147, with line refs.
3. Derived the divisor-test algebra [P]: (A) sign split, (B) source expansion, (C)
   $(1+h(p))/(1+h(p)/p)=p/(p-1)$, hence main term $N/\varphi(d)$ for both signs;
   relative-error exponent (D), positive exactly for fixed $\theta<1$ with
   $\eta<(1-\theta)/(2(2-\theta))$.
4. Implemented and ran the numerical countermodel in `/tmp/opencode/b003/countermodel.py`
   at $X=10^5$, $\theta=0.6$, $\eta=0.1$; output captured in
   `/tmp/opencode/b003/countermodel_output.txt`. Real numbers: 0 primes in plus support,
   $\sum_p a^+_p=0.0$; 337 divisor tests with summed absolute error 14007 < predicted
   50119; bilinear $B^+/U^+=1.000000000000000$ and $B^-/U^-=-1$ exactly over 11449 pairs.
5. Wrote `audit/B003_PARITY_ANALYSIS.md` with tagged claims, real output, and a `Verdict` section.
6. Verdict [I]: strict domination cannot be deduced from the linear/RH/automorphic tests
   that the plus model passes, because $B^+=U^+$ identically there. This rejects a class
   of deductions only; it does not rule out an independent bilinear theorem for genuine
   $\Lambda$ coefficients, and it is not a logical independence result.

## Honest status

- No Lean, no kernel check, no proof claim, no `map/` status change. Claims tagged [Q]/[P]/[I]/[U];
  the RH-dependent (5)/(7) remain [U]/conditional per `audit/REPO_AUDIT.md` C21.
- No git operations. No writes to `map/`, `lean/`, `checker/`, `news/`, or the cloned repo.
- Lease released at end with reason `analysis_complete_no_proof`.
- Expected parent re-verification: `grep -n 'Verdict' audit/B003_PARITY_ANALYSIS.md`,
  `wc -c` both files, re-run `python3 /tmp/opencode/b003/countermodel.py`.

## Wave 2 — Astra (astra-w2-b003)

[P] 2026-11-27 16:36 UTC. Issues #3 and #9 and the local map are open. B-003 lease `b0bcd0672ae24911a0806ef0b068b4ba` acquired. The measurement will keep every k in the box and use the literal shifted Mangoldt weight. [Issue start](https://github.com/nisbenz/goldbach-grh-lean/issues/3#issuecomment-7223458874)

[P] The scratch scan reproduced all five Wave 1 genuine off-diagonals, then found positive values on all nine chosen highly composite or primorial multiples. The independently assembled local-product predictor agrees in sign on 273/288 sampled even targets. At N=30030 the uncentered genuine signed mass equals the entire raw mass. The common local factor from primes dividing N accounts for much of the observed family dependence. [P] The three requested declarations compile in the pinned v4.16.0 environment, with the allowed axiom list on each. The scratch port defines the missing arithmetic Liouville function explicitly.

[P] The full report, including durable copies of the measurement and Lean sources, is [B003_B012_ASTRA_DISPERSION_PROJECTION.md](../audit/B003_B012_ASTRA_DISPERSION_PROJECTION.md). The verified local compile exited 0 and printed exactly [propext, Classical.choice, Quot.sound] on each theorem. Source declarations matched; the banned-token scan was empty. [U] v4.36.0 strict checks are pending. The positive side of the genuine quadratic form, the genuine signed Type II cancellation and the Vaughan recombination remain open. [P] The desk released `b0bcd0672ae24911a0806ef0b068b4ba` with reason `missing_lemma`; both local blockers and GitHub issues were open on the final check. [Issue #3 findings](https://github.com/nisbenz/goldbach-grh-lean/issues/3#issuecomment-7223639224) · [Issue #9 cross-note](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7223641312)
