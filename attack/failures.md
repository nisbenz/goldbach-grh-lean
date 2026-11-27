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

### 2026-11-27 — B-012, transferring factorization cancellation to prime mass

- [P] On the balanced factorization range d,k>1, all products counted by (U−B)/2 have at least three prime factors. On the cube-root-rough subset every product in this range has exactly two factors, so B=U for genuine weights as well. A small signed ratio on the unrestricted box does not imply rough prime mass.
- [I] Check the overlap of the negative-sign support with the detector before transferring a bilinear inequality. [U] A pointwise signed estimate for genuine shifted Mangoldt coefficients and a rough supply exceeding reflected higher-power contamination are still missing. [B-012 audit](audit/B012_BILINEAR_PARITY_ATTACK.md)

### 2026-11-27 — B-013, limits of the fiber prime-count test

[I] A positive surplus of prime counts across opposite quotient fibers forces a pair. The surplus was −1, −2 and −6 at N = 338, 578 and 1058 despite positive prime-only correlations. At N = 2p², sieving each fiber by 3, 5 and 7 shows that the surplus is negative for every p > 1190. The failure comes from comparing sparse prime supports with the entire fiber size. Use the surplus as a one-sided witness only. A general argument still needs a target-specific overlap estimate. [B-013 audit, §4](audit/B013_REFLECTION_HOLE_ATTACK.md)

[I] The B-013 handoff's release command used an unsupported `--reason` flag. The local CLI takes `release LEASE_ID REASON`; retrying with the positional reason returned `released`. Check `release --help` when using the handoff syntax in this checkout.

### 2026-11-27 — B-002, averaging over reflection centers

- [P] A cyclic weight can have zero convolution at a prescribed even center and convolution within a constant times √(M log M) of 2M at every other even center. Smoothing across target values therefore loses information needed for the specified target. The Hardy–Littlewood prediction and the direct scan also give predominantly negative centered differences.
- [I] For a transfer from averaged prime correlations, identify an independent one-sided bound for the average minus the value at the specified target. [U] ERH progression bounds and the available mean square leave that estimate open for the genuine von Mangoldt weights. [B-002 centering audit](audit/B002_ASTRA_CENTERING_ATTACK.md)

### 2026-11-27 — B-004 / B-014, fixed-target conductor estimate

- [P] At product cutoff `Y=q^2`, the optimized absolute tail and primitive-congruence count both allow `q^(1-2η+ε)`. Projecting the induced actual moment first eliminates the cutoff tail at `Y=N²/4` but leaves the single convolution `m+n=N`. A fixed narrow PSD profile has zero unit mass and positive model at 8, 16, 32 and 64.
- [I] Count a new gain only after bounding the signed subtracted residual on that target, or exhibiting a margin against the proper-power and detector remainders. For numerical comparisons, record the weight and its normalization. The original fixed-weight relation (16) has a conditional asymptotic remainder while the isolated variable-weight identity at twice a prime square deletes exactly one log-square. See [B-004 audit](/home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B004_B014_GWX_RATIOS_ATTACK.md).

### 2026-11-27 — B-015 / B-005, finite narrowing exhausts its supply

[P] The sharper Selberg coefficient 8 still gives a logarithmically divergent loss toward exponent 1. The prime-free plus model even realizes a normalized loss of at least log((a−1)/(b−1)) for fixed 1<b<a<2 before the extra rough cutoff. Capping the marked-divisor charge at one on the sharper cube-root-of-m range removes all slack but leaves the exact genuine rough prime count to estimate. [I] A successful switch needs an independent target-uniform signed estimate that excludes the model. [U] The analytic blockers remain open. [Full audit](audit/B015_B005_SIEVE_NARROWING_ATTACK.md)

### 2026-11-27 — B-010 / B-011, limitations of moment and full-line estimates

[P] A modulated interval realizes order √N coefficients of size comparable to N under the companion energy and supremum bounds. The resulting moment power p+1/2 is sharp for those inputs and still permits a negative coefficient at the chosen target. A full-line zero block admits a beta-integral bound of order T times two local zero-density factors, whereas the H1 finite arc damps a block exponentially in T. [I] Keep the actual integration interval and the target sign throughout any transfer to H1/H2. For scratch Lean modules record the local axiom audit and the vendored checker's project-path verdict separately. For Dirichlet Hardy-Z scans check primitivity before evaluation because FLINT aborts on imprimitive input. [Wave 2 audit](audit/B010_B011_ASTRA_ZEROPAIR_MOMENTS.md)

### 2026-11-27 — B-003 / B-012, sign of the genuine off-diagonal

[P] All five Wave 1 reference boxes had negative off-diagonals. The nine Wave 2 highly composite or primorial multiples all have positive values. At N=30030 all positive genuine raw mass has positive Liouville sign. The common unit restriction at primes dividing N and the signed row center explain much of the family dependence. [I] Test the positive side across factorizations of N and verify the actual Vaughan coefficient before transferring a projection estimate. [U] The pointwise genuine upper bound and the full Type I/II recombination remain open. [Wave 2 audit](audit/B003_B012_ASTRA_DISPERSION_PROJECTION.md)

### 2026-11-27 — B-007, false ladder PASS and limits of bounded replay

- [P] With explicit M=6 and L=99 the C++ first-rung search wrapped through zero and reported 18,446,744,073,709,551,557 as a prime ≤2. [I] Validate the lower domain before the search and recheck both endpoints independently before accepting a ladder.
- [P] One high-window HIP process exited on signal 11. Its cause remains unknown. A synchronized retry and three synchronized repeats passed with the CPU checksum. [I] Discard interrupted tiles and retain failed runs in the verification record.
- [P] The 2,000-witness-bound legacy comparison exceeded 16 seconds. The packed Lean 4.16 proof through 10,000 passed an exact-type kernel replay, but the vendored gate rejected its scratch module path before checking mathematics. [I] Keep local replay and project acceptance distinct. [U] A complete independent binary run through 4 × 10¹⁸ is still missing. [B-007 audit](audit/B007_COMPUTATIONAL_VERIFICATION_AUDIT.md)

### 2026-11-27 — B-011 / B-010, differentiated errors and unsigned energy

[P] The full-line zero-pair beta kernel differentiates both prime-counting error primitives, removing both reciprocal-zero weights. A bound for the primitive therefore gives no summable derivative tail by direct substitution. The companion model also has a genuine global error norm at least (1/√2 − 1/2 − o(1))√(N log N), excluding the proposed global norm repair. [I] Localize the differentiated explicit formula before applying a mean-value estimate. For H1/H2 keep the finite Farey windows and the target sign. [U] Removing heights above log⁴ N costs o(N), but the signed low-height residual remains open. [Wave 3 derivations](audit/B011_W3_PERSISTENT_BETA_PUSH.md)

### 2026-11-27 — B-004 / B-015 / B-005, Wave 3 threshold tests

[P] Smooth subtraction on a fixed balanced box eliminates the finer prime-square grid to square-root precision under Dirichlet GRH. The surviving grid retains the single-target Goldbach discrepancy. Lowering the rough cutoff raises the capped signed mass by the actual increase in rough mass to within twice the upper cutoff times log N. [I] Track this moving signed cost and the surviving fixed shift when testing a proposed margin. The switched upper sieve narrows the semiprime band, but its loss still diverges at the prime endpoint. [Wave 3 report](audit/B004_B015_W3_PERSISTENT_THRESHOLD_PUSH.md)

## B-005 / B-012 / B-015 · Wave 4 · 2026-11-27

[P] At common level one the switched lower-minus-upper margin is exactly minus twice the three-prime simplex integral. Its maximum is zero. A fixed exponent above one contradicts the progression main term on prime moduli larger than the target. [U] A genuine, target-uniform signed comparison on smaller factors from exponent 0.4383 to 1/2, or a one-sided semiprime-band saving with near-full distribution, is still missing. [I] Specify the comparison sequence, coefficient class and endpoints before transferring a Type II range to primes. [Derivation and obstruction](audit/B005_B012_W4_DECISIVE_PARITY_PHASE_DIAGRAM.md)

### 2026-11-27 — B-011 / B-002, mixed term and signed low-zero pairs

[P] On square-root Farey cells the primitive mixed Gauss product leaves one character sum with a cost of order √N per denominator even on a common central interval. Arbitrary overlap choices can also change the pole square by order N. [I] Specify the cells before using a signed center sum. Increasing the order to N^(2/3) makes the entire mixed term negligible. [U] On that dissection the missing estimate is a one-sided bound for distinct low-zero character pairs of large product conductor at each specified target. Their underlying field has squared energy ≫ N log N. [Wave 4 report](audit/B011_B002_W4_DECISIVE_LOWZERO_PUSH.md)

## 2026-11-27 — Wave 5 Phase 1 Three-Strike Breakthrough Gate (B-012, B-004/B-014, B-011)
- **B-012 / B-005 (Strike 1A):** Audited Lichtman (`arXiv:2611.28392v1`, 20 Nov 2026) and Pascadi (`arXiv:2611.34917v1`, 25 Nov 2026) from arXiv LaTeX. *Exact obstacles:* (1) Lichtman's exact prime-interval partition requires prime divisors in $\ge 3k \ge 3$ intervals, so every semiprime has $T(qr)=0$ identically, and Goldbach reflection turns determinant $a-b$ into $N(b-a)$ outside the kernel cutoff; (2) under prime EH, the optimized Selberg square for the central semiprime band has infimum coefficient exactly $2$, while direct Cauchy–Schwarz needs a normalized off-diagonal $< 4$ not given by Pascadi's cited theorems.
- **B-004 / B-014 (Strike 1B):** Audited Lee (`arXiv:2610.32672v2`), GWX (`arXiv:2611.18825v1`), and Pascadi (`arXiv:2611.34917v1`) from arXiv LaTeX. *Exact obstacles:* (1) Lee's opposing time weights depend on $m/n$ ratios and do not transfer to Goldbach reflection $N-p$ (Mellin shift $\asymp N \gg U^{1/4}$); (2) at fixed displacement $\eta = 1/16$, GWX requires $\vartheta < 1 - 2\eta = 7/8$ strictly while ERH hits $7/8 + \varepsilon$ ($29/32 + \varepsilon$ across Lee's $[3/64, 5/64]$ box); (3) Pascadi's $207/389$ is height-aspect with $O(1/\log T)$ numerator shifts and falls outside the conductor block.
- **B-011 / B-002 (Strike 1C):** *Exact obstacle:* Reversing the explicit formula and summing over $q$ first at $Q = \lfloor N^{2/3}\rfloor$ under ERH keeps the ordered von Mangoldt Goldbach coefficient at the zero frequency, forcing the nonzero frequencies to sum to $-N\mathfrak{S}(N)/e + O(N/\sqrt{\log N})$ — making an $o(N)$ nonzero-frequency bound mathematically impossible. Complete critical-line root isolation at $N=128,160,192$ confirms within-modulus cancellation beats across-modulus cancellation, leaving pointwise signed control open.
- **Derived rule:** All four modern attack families (ERH ultra-low zeros + cross-$q$ summation, GWX/Lee fixed-shift ratios + Pascadi, Ford–Maynard/Selberg central semiprime dispersion, and LWW/Lichtman Möbius cancellation) now have exact, verified structural barrier proofs. Stop spending research tokens on these blocked routes; proceed to Phase 2 Branch C (checked-ground Lean hardening & final closure report) unless a genuinely new mathematical idea appears.

## 2026-11-27 — Wave 6 New-Frontiers Strikes (B-005 Function-Field Transfer, B-012 GL_2 Determinant)
- **B-005 (Strike 2A):** Dissected GWX's unconditional function-field Goldbach proof (`m4.tex:2778-3265`) and Reciprocal Ratios/Chowla (`m4.tex:3475-3577`). *Positive structural insight:* The exact cutoff identity transfers to $\mathbb{Z}$, already gives the full $N\mathfrak{S}(N)+o(N)$ main term at unconditional BV cutoff, and its long-divisor tail $T_D$ escapes LWW/Lichtman's semiprime zero-support wall ($\ge 1/2 - o(1)$ squarefree quotients hit every separated prime band). *Exact obstacle:* Bounding $T_D$ rowwise costs $O(L^2)$ (requiring uniform reflected saving $L^{-2}$, vs Lichtman's fixed-shift $L^{-1/2+\varepsilon}$), while a second divisor switch gives two primitive affine forms $d=u+qt, z=v-kt$ of determinant $+N$ where no $\mathbb{Z}$-analogue of $\ell$-adic discriminant cohomology is known (even under ERH or GWX's fixed-$h$ Chowla appendix).
- **B-012 (Strike 2B):** Attacked the Wave 5 Cauchy–Schwarz off-diagonal ($o_N < 4$) via $\mathrm{GL}_2$ spectral theory on $q_2 p_1 - q_1 p_2 = N(q_2 - q_1)$. *Exact obstacles:* (1) $s_N^2 - o(1) \le o_N \le 2s_N + o(1)$ under prime EH makes $o_N < 4 \iff s_N < 2$ strictly, with cofactor sieve squares hitting exact infimum $4$; (2) $h\overline{q_1} \equiv -N \pmod{q_2}$ kills the inverse $q_1$ Kloosterman phase after Poisson summation, collapsing the $\mathrm{GL}_2$ spectral twist back to three correlated prime weights across unconditional, Selberg ($\theta_2 = 0$), and $\mathrm{GL}_2$ Grand RH.
