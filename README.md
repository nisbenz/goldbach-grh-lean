> **Coordinated attack framework (2026-11-28, Waves 0–38).** A local, verifier-first attack system lives in
> [`attack/`](attack/) with the binding agent protocol at [`AGENTS.md`](AGENTS.md): a claim/blocker
> map, a lease desk, a kernel-checker (including a vendored Apache-2.0 checker with attribution),
> arXiv news monitoring, a dashboard, and a failure log. **Pointwise Strong (Binary) Goldbach remains
> OPEN** (including under ERH, ordinary prime EH, and $\mathrm{GL}_2$ Grand RH). As of Wave 38, the
> map records **54 checked claims** (out of 60), **6 resolved blockers**, **11 open blockers** (GitHub
> issues `#2`–`#12`), and **32 kernel-checked Lean 4 files across Waves 7–38 (`307` public theorems/lemmas
> + `51` private helpers = `358` verified declarations, zero `sorry`, zero `native_decide`, standard
> axioms `[propext, Classical.choice, Quot.sound]` only)**. See [`attack/map/claims.json`](attack/map/claims.json),
> [`attack/map/blockers.json`](attack/map/blockers.json), and [`attack/failures.md`](attack/failures.md)
> for the exact state.

# goldbach-grh-lean

Explicit GRH-conditional proofs, `sorry`-free Lean 4 (`v4.16.0` + Mathlib) formalizations, independent 60-digit interval-arithmetic & computational verifiers, and a systematic Strong Goldbach audit framework for:

1. **Weak (Ternary) Goldbach Conjecture under GRH:** Every odd integer $N \ge 7$ is the sum of three primes. *(In `lean/WeakGoldbach/Main.lean`, `weak_goldbach_theorem` compiles cleanly on Lean `v4.16.0` with 7 explicit axioms: 5 analytic GRH axioms + `binaryGoldbach_4e18` + `certified_prime_ladder_1e22`.)*
2. **Binary (Strong) Goldbach Exceptional-Set Theorem under GRH:** For every $X \ge 4$, the number $E(X)$ of even integers in $[4, X]$ that are *not* sums of two primes satisfies
   $$E(X) \le 2{,}000{,}000\,\sqrt{X}\,(\log X)^3,$$
   and hence $E(X)/X \to 0$ as $X \to \infty$ (almost all even integers are sums of two primes). *(In `lean/WeakGoldbach/BinaryExceptional.lean`, `binary_goldbach_exceptional_bound` and `binary_goldbach_density_one` compile cleanly on Lean `v4.16.0` with 11 explicit axioms. Pointwise Strong Goldbach for all even $N > 2$ remains open.)*

## What Is Actually Proved in This Repository

To keep checked ground strictly separate from open problems (per [`AGENTS.md`](AGENTS.md) §0), every result in this repository falls into one of three verified tiers:

### 1. Machine-Checked in Lean 4 (`v4.16.0`, zero `sorry`, allowed axioms only)
Only `propext`, `Classical.choice`, and `Quot.sound` — **no custom axioms**:
- **Unconditional Binary Goldbach up to $50{,}000$:** `BinaryGoldbachUpTo 50000` kernel-verified via a 51-page packed prime-pair certificate (`40.3s` build, `52.2s` independent kernel replay; scaled $5\times$ from $10{,}000$) ([Wave 3 report](attack/audit/B007_W3_FIX_AND_SCALING.md)).
- **Core assembly, Pratt soundness & exceptional-set engine (`lean/WeakGoldbach/`):**
  - `weakGoldbach_complete` (gluing binary Goldbach + prime ladder + asymptotic bound),
  - `prime_of_lucas_trace` (soundness of flat-trace Pratt primality certificates from Mathlib, plus 5 ladder rungs kernel-replayed in `1.48s`),
  - `threshold_inequality` (explicit analytic threshold over $\mathbb{R}$ for $N \ge 10^{22}$),
  - `BinaryExceptionalCore` (Finset Chebyshev/Markov inequalities, dyadic geometric summation, and asymptotic density-1 reduction).
- **54 checked claims in [`attack/map/claims.json`](attack/map/claims.json):** includes H1 major-arc rational certificates, dyadic/prime-power bounds, 8 Wave 1–2 Lean `v4.16.0` micro-lemmas, and **32 complete Lean 4.33.1 formalization files across Waves 7–38** (all verified with zero `sorry`, zero `native_decide`, and `#print axioms` strictly within `[propext, Classical.choice, Quot.sound]`):

| Wave | File | Verified Decls | Key Proven Theorems & Lemmas |
|---|---|---:|---|
| W7 | [`TailBarrier.lean`](attack/lean/Goldbach/TailBarrier.lean) | 5 | `reflection_energy_split`, `fComp_bounds`, `fComp_zero_goldbach`, `fComp_progression_diff_le`, `fComp_shortDivisorSum_close` |
| W8 | [`MellinEulerCriterion.lean`](attack/lean/Goldbach/MellinEulerCriterion.lean) | 20 | `eulerFactor_eq_moebius_sum`, `bilateralEuler_eq_crt_sum`, `bilateralEuler_hyperbola_split`, `bilateral_mellin_euler_goldbach_criterion`, `oneSided_mellin_euler_goldbach_criterion` |
| W9 | [`AntiSymmetricEuler.lean`](attack/lean/Goldbach/AntiSymmetricEuler.lean) | 24 | `antiSymFactor_eq_closed_form`, `antiSymFactor_eq_zero_of_squarefree_even`, `antiSym_bilateral_composite_mono`, `bilateralAntiSym_quadrant_split`, `bilateral_antiSym_quadrant_goldbach_criterion`, `bilateral_oddSqfree_goldbach_criterion` |
| W10 | [`ThreeRegionHyperbola.lean`](attack/lean/Goldbach/ThreeRegionHyperbola.lean) | 9 | `three_region_split`, `crtPairCount_eq_zero_of_not_dvd`, `card_mod_Ico_bounds`, `crtPairCount_approx`, `gcd_dvd_indicator_eq_sum_psi`, `regionII_bv_modulus_bound` |
| W11 | [`RegionIIIParity.lean`](attack/lean/Goldbach/RegionIIIParity.lean) | 10 | `vaughan_moebius_identity`, `muTypeII_eq_bilinear_sum`, `regionIII_vaughan_split`, `parity_annihilates_antiSym_of_squarefree`, `parity_three_region_eq_nonSqfree_sum` |
| W12 | [`KloostermanMaster.lean`](attack/lean/Goldbach/KloostermanMaster.lean) | 6 | `kloosterman_reciprocity_mod_int`, `archimedean_reciprocity_factor_le_one`, `elem_weil_clears_asymmetric_point`, `bettin_chandee_clears_balanced_diagonal`, `optimal_kloosterman_clears_below_one`, `four_region_split` |
| W13 | [`DampedBoundaryEuler.lean`](attack/lean/Goldbach/DampedBoundaryEuler.lean) | 19 | `dampedFactor_eq_closed_form`, `damped_bilateral_composite_mono`, `damped_cofactor_weight_bound`, `damped_k11_slice_unsigned_bound`, `damped_bilateral_goldbach_criterion` |
| W14 | [`SecondOrderDampedEuler.lean`](attack/lean/Goldbach/SecondOrderDampedEuler.lean) | 23 | `secondOrderFactor_eq_closed_form`, `secondOrder_cofactor_weight_bound`, `secondOrder_k11_slice_o_n_bound`, `secondOrder_bilateral_composite_mono`, `secondOrder_bilateral_goldbach_criterion` |
| W15 | [`MobiusDualCore.lean`](attack/lean/Goldbach/MobiusDualCore.lean) | 11 | `sum_log_mul_moebius_eq_vonMangoldt`, `mobiusDual_add_tail_eq_vonMangoldt`, `mobiusDual_conv_le_l2_norm`, `secondOrder_mixed_k1_strip_bound`, `secondOrder_small_cofactor_eq_mobiusDual_add_err` |
| W16 | [`DirectAbelBV.lean`](attack/lean/Goldbach/DirectAbelBV.lean) | 11 | `congruence_div_gcd_iff`, `direct_bv_modulus_improves_after_gcd`, `discrete_abel_summation`, `w2_antitone_in_d1`, `direct_bv_reaches_boundary_half`, `five_region_secondOrder_split`, `global_k1_slice_cauchy_schwarz_bound` |
| W17 | [`RegionICRTBound.lean`](attack/lean/Goldbach/RegionICRTBound.lean) | 12 | `unweighted_ap_discrepancy_le_one`, `weighted_ap_discrepancy_le`, `crt_exists_unique_residue`, `crt_weighted_discrepancy_le`, `regionI_secondOrder_crt_error_bound` |
| W18 | [`ZRoughSmallCofactorKill.lean`](attack/lean/Goldbach/ZRoughSmallCofactorKill.lean) | 9 | `zRough_prime_of_le_sq`, `zRough_mobiusDual_eq_neg_mu_sum_primes`, `zRough_mobiusDual_sq_eq_prime_pair_sum`, `zRough_mertens_margin_strict`, `zRough_filter_goldbach_criterion` |
| W19 | [`SelbergWeightedEuler.lean`](attack/lean/Goldbach/SelbergWeightedEuler.lean) | 8 | `selbergWeight_nonneg`, `selbergWeight_eq_one_of_prime_gt`, `selbergWeight_eq_lcm_sum`, `selberg_regionI_crt_modulus_bound`, `selbergWeighted_mobiusDual_conv_le_l2`, `selbergWeighted_goldbach_criterion` |
| W20 | [`StrongGoldbachMaster.lean`](attack/lean/Goldbach/StrongGoldbachMaster.lean) | 5 | `secondOrderFactor_div_sigma`, `weightedSecondOrderDiff_eq_divisor_sum`, `master_exact_six_region_decomposition`, `strong_goldbach_master_reduction`, `master_budget_closes_of_interior_saving` |
| W21 | [`VaughanTypeIClearing.lean`](attack/lean/Goldbach/VaughanTypeIClearing.lean) | 9 | `linear_congruence_unique_mod`, `typeI_progression_weighted_error_le`, `typeI_box_total_error_bound`, `typeI_clears_beyond_half`, `typeI_tight_regionIII_area_exact` |
| W22 | [`BilinearLargeSieve.lean`](attack/lean/Goldbach/BilinearLargeSieve.lean) | 8 | `w2_exact_rank2_separation`, `two_step_gcd_congruence_reduction`, `bilinear_large_sieve_glues_with_wave16_zero_gap`, `wright1_punches_into_half_square`, `secondOrder_pure_square_decomposition` |
| W23 | [`DispersionAndDualTypeI.lean`](attack/lean/Goldbach/DispersionAndDualTypeI.lean) | 5 (+4) | `dual_typeI_box_error_bound`, `typeI_x_typeI_elementary_areas_exact`, `dispersion_cauchy_schwarz_reduction`, `dispersion_double_congruence_crt`, `dispersion_reciprocity_phase_mod_int` |
| W24 | [`SingularSeriesMainTerm.lean`](attack/lean/Goldbach/SingularSeriesMainTerm.lean) | 6 | `bilateral_crt_local_factor_eq_singular_series`, `weierstrass_prod_one_sub_ge`, `even_recip_sq_sum_lt_one_sixth`, `goldbach_singular_series_gt_five_fourths`, `secondOrder_linear_term_eq_two_vonMangoldt`, `secondOrder_deriv_term_eq_neg_two_log_vonMangoldt` |
| W25 | [`PureSquareFourierAndDiffSq.lean`](attack/lean/Goldbach/PureSquareFourierAndDiffSq.lean) | 11 | `weighted_diff_sq_cauchy_schwarz`, `discrete_fourier_orthogonality`, `pure_square_fourier_representation`, `dft_parseval_sq`, `pure_square_parseval_mean_square_bound`, `master_pure_square_diffSq_goldbach_criterion` |
| W26 | [`VinogradovMinorArcs.lean`](attack/lean/Goldbach/VinogradovMinorArcs.lean) | 16 | `distToInt_norm_e_sub_one_ge`, `geometric_exp_sum_bound`, `bilinear_exp_sum_min_bound`, `vinogradov_block_harmonic_bound`, `exceptional_set_markov_bound` |
| W27 | [`SimplexSelbergWeight.lean`](attack/lean/Goldbach/SimplexSelbergWeight.lean) | 8 (+1) | `simplexSelberg_nonneg`, `simplexSelberg_eq_one_of_prime_pair_gt`, `simplexSelberg_bilinear_expansion`, `simplexSelberg_crt_modulus_bound`, `simplex_selberg_variational_factor_two`, `symm_2d_diff_sq_cauchy_schwarz`, `simplexSelberg_goldbach_criterion` |
| W28 | [`HeathBrownWellFactorable.lean`](attack/lean/Goldbach/HeathBrownWellFactorable.lean) | 7 | `truncMoebius_remainder_vanishes`, `conv_pow_vanishes_le_pow`, `heath_brown_moebius_identity`, `greedy_well_factorable_split`, `greedy_triply_well_factorable_split`, `well_factorable_three_fifths_area_exact` |
| W29 | [`SemiprimeAnnihilationAndSwitch.lean`](attack/lean/Goldbach/SemiprimeAnnihilationAndSwitch.lean) | 6 | `semiprime_divisors_gt_cutoff`, `cubeRough_primeFactorsList_length_le_two`, `semiprime_chen_switching_sum`, `moebius_cofactor_product_eq_mu_sq`, `balanced_semiprime_annihilation_geometry_exact` |
| W30 | [`SquarefreeAndAffineChowla.lean`](attack/lean/Goldbach/SquarefreeAndAffineChowla.lean) | 8 | `moebius_sq_eq_sum_sq_divisors`, `squarefree_count_exact_identity`, `squarefree_count_error_le_sqrt`, `affine_chowla_parametrization`, `affine_chowla_determinant_identity`, `affine_chowla_length_lower_bound_on_35_square` |
| W31 | [`CofactorShiftDispersion.lean`](attack/lean/Goldbach/CofactorShiftDispersion.lean) | 5 (+1) | `cofactor_shift_dispersion_split`, `cofactor_shift_diagonal_count_bound`, `cofactor_shift_diagonal_exponents_clear_interior`, `off_diagonal_elimination_identity`, `cofactor_shift_any_o1_saving_suffices` |
| W32 | [`FareyMoebiusDuality.lean`](attack/lean/Goldbach/FareyMoebiusDuality.lean) | 10 | `progression_eq_finite_fourier_sum`, `farey_primitive_partition_sum`, `moebius_mul_eq_ite_coprime`, `farey_moebius_duality_exact`, `farey_moebius_frequency_localization_bound` |
| W33 | [`RamanujanSingularSeriesDuality.lean`](attack/lean/Goldbach/RamanujanSingularSeriesDuality.lean) | 7 (+6) | `ramanujanSum_eq_complex_exp_sum`, `ramanujanSum_prime`, `ramanujan_local_euler_eq_goldbach_singular_series`, `ramanujan_sum_orthogonality`, `divisor_moebius_ramanujan_expansion_exact`, `ramanujan_parseval_energy` |
| W34 | [`RamanujanFareyConvolution.lean`](attack/lean/Goldbach/RamanujanFareyConvolution.lean) | 7 (+16) | `ramanujan_conv_period_exact`, `ramanujan_conv_interval_exact`, `ramanujanSum_abs_le_sum_divisors_gcd`, `ramanujan_diagonal_low_bound`, `ramanujan_diagonal_tail_bound`, `farey_distinct_separation_lower_bound`, `selberg_ramanujan_reflection_identity` |
| W35 | [`CofactorLatticeChowla.lean`](attack/lean/Goldbach/CofactorLatticeChowla.lean) | 7 (+3) | `coupled_dispersion_modulus_bounds`, `coupled_dispersion_step_dvd`, `coupled_dispersion_lattice_parametrization`, `coupled_dispersion_chowla_determinant`, `coupled_dispersion_chowla_nondegenerate`, `progression_count_in_dyadic_ge`, `chowla_poly_length_geometry_exact` |
| W36 | [`FareyAliasingSharpBound.lean`](attack/lean/Goldbach/FareyAliasingSharpBound.lean) | 5 (+8) | `geomExpSum_norm_le_inv_two_distToInt`, `farey_diff_fiber_card_le_gcd`, `sum_inv_two_min_mod_le_harmonic`, `farey_pair_geom_sum_bound`, `offDiagFareyForm_sharp_bound` |
| W37 | [`CotangentHilbertGoldbach.lean`](attack/lean/Goldbach/CotangentHilbertGoldbach.lean) | 4 (+11) | `symmetrized_geom_kernel_eq_cot`, `offDiagFareyForm_re_eq_cotangent_hilbert`, `sin_cot_sum_eq_sawtooth_exact`, `eisenstein_cotangent_sum_exact` |
| W38 | [`PureIntegerGoldbachSawtooth.lean`](attack/lean/Goldbach/PureIntegerGoldbachSawtooth.lean) | 6 (+1) | `crt_main_term_eq_ramanujan_diagonal`, `mod_count_exact_and_discrepancy_lt_one`, `crtDiscrepancy_abs_lt_one`, `pure_integer_goldbach_crt_ramanujan_identity`, `pure_integer_goldbach_error_le_l1_sq`, `puresquare_crt_count_zero_or_one` |

  *(Counts show `public (+private)` declarations; total across Waves 7–38: **307 public + 51 private = 358 verified declarations**, with paired audit docs [`attack/audit/B013_W7_*`](attack/audit/) through [`attack/audit/B013_W38_PURE_INTEGER_GOLDBACH_SAWTOOTH.md`](attack/audit/B013_W38_PURE_INTEGER_GOLDBACH_SAWTOOTH.md).)*

### 2. Machine-Checked Conditional Theorems in Lean 4 (`v4.16.0`, zero `sorry`, explicit axioms)
- **`weak_goldbach_theorem`** (`lean/WeakGoldbach/Main.lean`): every odd $N \ge 7$ is a sum of three primes, conditional on **7 explicit axioms** (5 analytic GRH axioms + `binaryGoldbach_4e18` + `certified_prime_ladder_1e22`).
- **`binary_goldbach_exceptional_bound` & `binary_goldbach_density_one`** (`lean/WeakGoldbach/BinaryExceptional.lean`): $E(X) \le 2{,}000{,}000\sqrt{X}(\log X)^3$ for all $X \ge 4$ and $E(X)/X \to 0$, conditional on **11 explicit axioms**.

### 3. New Mathematical Theorems & Barrier Proofs from Waves 1–6 (Analytic + Arb/SymPy-Verified, Not Yet in Lean)
Six distinct modern routes — including direct LaTeX source audits of late-2026 arXiv preprints (`arXiv:2606.05224v2` Li–Liu, `arXiv:2610.20242v2` Lü–Wang–Wu, `arXiv:2610.32672v2` Lee, `arXiv:2611.18825v1` Gou–Wang–Xu, `arXiv:2611.28392v1` Lichtman, `arXiv:2611.34917v1` Pascadi) — have been proved/audited in [`attack/audit/`](attack/audit/):

1. **Ultra-Low-Zero Reduction & Impossibility Walls under ERH (`B-002`, `B-010`, `B-011`):**
   - Saved a full $\sqrt{T}$ on the full-line zero-pair block ($T^{3/2}\log^2 T \to O(T\log(2dT)\log(2d'T))$, and $O(N\log N)$ at $T \asymp N$) ([Wave 2](attack/audit/B010_B011_ASTRA_ZEROPAIR_MOMENTS.md), [Wave 3](attack/audit/B011_W3_PERSISTENT_BETA_PUSH.md)).
   - Proved that under Dirichlet ERH at Farey order $Q = \lfloor N^{2/3}\rfloor$, all zeros with $|\gamma| \ge 2\log\log N$, all pole–zero cross terms, and $\beta$-integration drop into $o(N)$, collapsing Strong Goldbach to a single scalar criterion $\liminf \mathcal{P}_N^\circ > -1/3$ ([Wave 4](attack/audit/B011_B002_W4_DECISIVE_LOWZERO_PUSH.md)).
   - Proved three exact barriers on that route: global $L^r$ Hölder repair is impossible ($\|S-M\|_r \gg \sqrt{N\log N}$), fixed-$q$ unitary norms fail, and summing over $q$ first leaves a linear resonance forcing nonzero frequencies to sum to $-N\mathfrak{S}(N)/e + O(N/\sqrt{\log N})$ ([Wave 5](attack/audit/B011_W5_CROSSQ_LOWZERO_STRIKE.md)).
2. **Exact Switched-Sieve Parity Phase Diagram & Semiprime Thresholds (`B-003`, `B-005`, `B-012`, `B-015`):**
   - Proved exact parity conservation for switched sieves at level $\theta \to 1^-$: $M(\beta, 1^-) = -2I_3(1/\beta) \le 0$ (exact ceiling $0$ on $[1/3, 1/2]$, and $\theta > 1$ impossible on prime moduli $q > N$).
   - Proved (200-bit Arb) that under unconditional BV Type I, signed Type II on the **6.17% band $[N^{0.43835}, \sqrt{N}]$** suffices for Strong Goldbach (prime-free obstruction at $0.47560$), and under ordinary prime EH **any** upper-bound constant $c < 2$ on one narrow central semiprime band suffices ([Wave 4](attack/audit/B005_B012_W4_DECISIVE_PARITY_PHASE_DIAGRAM.md)).
   - Proved that optimized Selberg squares hit exact infimum $2$ ($S_\delta/\mathrm{HL}_\delta \to 2$ on any exception sequence), while both Lü–Wang–Wu (`2610.20242v2`) and Lichtman (`2611.28392v1`) assign zero active weight to every semiprime and break under reflection determinant $N(b-a)$ ([Wave 5](attack/audit/B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)).
   - Sharpened the Li–Liu $(1+1.9)$ narrowing Selberg constant $50\times$ (`200 → 8 → 4`) and raised the `B-005` unsigned cutoff baseline by $+81.7\%$ ($\beta = 2/9 \to 1/5$) ([Wave 3](attack/audit/B004_B015_W3_PERSISTENT_THRESHOLD_PUSH.md)).
3. **Integer Transfer of GWX's Unconditional Function-Field Goldbach Cutoff (`B-005`):**
   - Transferred GWX's (`2611.18825v1`) unconditional $\mathbb{F}_q[T]$ divisor split to $\mathbb{Z}$: proved that even at the **unconditional BV cutoff**, short divisors already supply the full $N\mathfrak{S}(N) + o(N)$ main term and the long tail $T_D$ escapes the LWW/Lichtman semiprime zero-support wall ($\ge 1/2 - o(1)$ squarefree quotients hit every separated prime band), establishing exact aggregate (eq. 5), $L^{-2}$ rowwise (eq. 7), and determinant-$+N$ two-form (eq. 9) criteria ([Wave 6](attack/audit/B005_W6_FUNCTION_FIELD_TRANSFER_STRIKE.md)).
4. **Dirichlet $2/2$ Ratios & $\mathrm{GL}_2$ Spectral Walls (`B-004`, `B-014`, `B-012`):**
   - Proved directly from source TeX that GWX requires $\vartheta < 1 - 2\eta$ strictly ($7/8$ at $\eta=1/16$) while ERH sits at $1 - 2\eta + \varepsilon$ ($29/32 + \varepsilon$ on Lee's $[3/64, 5/64]$ box), Lee's $m/n$ time weights do not transfer to Goldbach reflection, and Pascadi's $207/389$ (`2611.34917v1`) is height-aspect with $O(1/\log T)$ shifts ([Wave 5](attack/audit/B004_W5_LEE_GWX_PASCADI_STRIKE.md)).
   - Proved under prime EH that $s_N^2 - o(1) \le o_N \le 2s_N + o(1)$ makes Cauchy–Schwarz off-diagonal $o_N < 4$ strictly equivalent to $s_N < 2$, and $h\overline{q_1} \equiv -N \pmod{q_2}$ kills the inverse-$q_1$ Kloosterman phase, collapsing the $\mathrm{GL}_2$ twist across unconditional, Selberg ($\theta_2 = 0$), and $\mathrm{GL}_2$ Grand RH ([Wave 6](attack/audit/B012_W6_GL2_DETERMINANT_STRIKE.md)).
5. **Verified Computational Fixes & Audits (`B-007`):**
   - Caught and fixed an unsigned-underflow false-PASS soundness bug in `verify/verify_finite.cpp` (17 regression tests passing), independently verified binary Goldbach natively to $5 \times 10^7$ (`0.09s`), and replayed all 2,501 Pratt certificates (86,507 nodes) in `verify/ladder_certs.json.gz`.

### What Is NOT Proved (Work Left to Solve Strong Goldbach)
**Pointwise Strong (Binary) Goldbach for all even $N \ge 4$ remains OPEN** (including under ERH, prime EH, and $\mathrm{GL}_2$ Grand RH). Closing it requires:
- **At least one genuinely signed / parity-breaking prime theorem** breaking one of the remaining walls:
  - *PureSquare / Modular-Hyperbola Discrepancy (Waves 31–38):* any $o(1)$ bilinear saving in the modular-hyperbola discrepancy sum $\sum_{m_1, m_2 > M} \mu(m_1)\mu(m_2)\log(m_1)\log(m_2)\,(\mathbf{1}_{x_0 < n} - n/(m_1 m_2))$ on $[3/5, 1]^2$, **or** equivalently in Wave 31/35's 4-parameter averaged non-degenerate binary Chowla sum `OffDiag_{k₁ ≠ k₁'}` (or Wave 34's `offDiagFareyForm` on the top Farey shell $q > \sqrt{n}$), **or**
  - *Analytic (ERH):* pointwise signed lower bound $\liminf_{2\mid N\to\infty} \mathcal{P}_N^\circ > -1/3$ on ultra-low zeros $|\gamma| < 2\log\log N$ at $Q = \lfloor N^{2/3}\rfloor$, **or**
  - *Sieve / Bilinear:* signed Type II on $[N^{0.43835}, \sqrt{N}]$ (under BV), **or** $c < 2$ on one central semiprime band (under prime EH), **or** uniform $L^{-2}$ reflected-prime Möbius saving / power-saving two-form cancellation of determinant $+N$ on the BV long-divisor tail $T_D$, **or**
  - *Ratios:* strict power saving $\vartheta < 1 - 2\eta$ in $2/2$ Dirichlet $L$-function ratios uniformly over $q \mid N$.
- **Classical analytic inputs in Lean:** PNT for $\mu$, Bombieri–Vinogradov, BFI ($4/7$), and Maynard II ($3/5$) remain external analytic hypotheses in `StrongGoldbachMaster.lean` and have not been formalized from scratch in Mathlib.
- **Effective onset & computational bridge (`B-007`):** explicit constants establishing $N_0 \le 4\times 10^{18}$ (or bridging $[4\times 10^{18}, N_0]$) plus independent machine-checked verification of the finite range.
- **Engineering / Lean hygiene (non-blocking for math, valuable for formal ground):** upstreaming the Wave 1–3 Lean `v4.16.0` micro-lemmas and `BinaryGoldbachUpTo 50000` into `attack/lean/`, and discharging `certified_prime_ladder_1e22` in `lean/WeakGoldbach/Main.lean` (7 $\to$ 6 axioms).

## Repository Layout

- **[proof/](proof/)**
  - `proof/weak_goldbach_proof.md` — Self-contained explicit GRH proof of Weak Goldbach for all odd $N \ge N_0 = 10^{22}$ using exponential weight $e^{-n/X}$ ($X = N/2$, strictly-prime margin $> 0.083\,X^2$).
  - `proof/binary_goldbach_exceptional_proof.md` — Explicit GRH proof of $E(X) \le 2{,}000{,}000\sqrt{X}(\log X)^3$ for all $X \ge 4$ via Bessel's inequality, a unified divisor-average bound for both truncation tails, Markov/Chebyshev exception counting, and dyadic summation from $X_0 = 4 \times 10^{18}$.
  - `proof/strong_goldbach_research.md` — Pointwise Strong Goldbach analysis under Dirichlet GRH: $1/4$ mean-square gap, zero-pair $T^{3/2}\log^2 T$ block, prime-free parity countermodel to every level $< 1$, Fourier reflection-hole counterexample, and three verified conditional reductions (H1/H2/H3) reaching $4 \times 10^{18}$.
  - `proof/strong_goldbach_erh_attack.md` — Analysis under ERH + Grand RH + 2026 literature (including Lü–Wang–Wu `arXiv:2610.20242v2`), automorphic-RH parity survival theorem, smooth reflected $d_2,d_2$ benchmark, and subcritical $z = N^{2/9}$ & Chen-set one-sided reductions.
  - `proof/strong_goldbach_nov2026_ratios_attack.md` — Analysis of the Nov 2026 Gou–Wang–Xu Dirichlet 2/2 Ratios route (`arXiv:2611.18825v1`) and Pascadi Kloosterman bounds (`arXiv:2611.34917v1`), critical $q^{1-2\eta}$ barrier, and weakened moving-line & finite-endpoint one-sided criteria.
  - `proof/strong_goldbach_persistent_push.md` — Deep synthesis: exact arithmetic subtraction of the GWX model inside smooth test sums, Pascadi + Selberg ($\lambda_1 \ge 1/4$) fixed-conductor analysis, obstructions to positive-definite/extremal sum kernels, sieve continuity narrowing of Li–Liu (`arXiv:2606.05224v2`), and sparse-conductor reflection-hole models at $2^k$ and $2p^2$.
- **[lean/](lean/)** — Lean 4 (`v4.16.0`) + Mathlib formalization (`lake build` passes with zero `sorry`s):
  - `WeakGoldbach/Defs.lean` — Core definitions (`IsSumOfTwoPrimes`, `IsSumOfThreePrimes`, `BinaryGoldbachUpTo`, `WeakGoldbachFrom`, `WeakGoldbachConjecture`, `PrimeLadder`).
  - `WeakGoldbach/PrimeLadder.lean` — Zero-axiom gluing proof `weakGoldbach_complete`.
  - `WeakGoldbach/Pratt.lean` — Zero-axiom soundness proof of flat-trace Pratt primality certificates (`prime_of_lucas_trace`) from Mathlib's `lucas_primality`.
  - `WeakGoldbach/Analytic.lean` — Kernel-verified Lemma 6 (`threshold_inequality` over $\mathbb{R}$ for all $N \ge 10^{22}$), `isSumOfThreePrimes_of_R_prime_pos`, and assembly `weakGoldbachFrom_N0`.
  - `WeakGoldbach/Main.lean` — Final theorem `weak_goldbach_theorem : WeakGoldbachConjecture` and `#print axioms` audit.
  - `WeakGoldbach/BinaryExceptionalCore.lean` — Zero-axiom Finset Chebyshev (`L²`) & Markov (`L¹`) inequalities, dyadic geometric summation `global_bound_of_dyadic_sqrt_log`, and asymptotic density-1 theorem `density_one_of_sqrt_log_bound`.
  - `WeakGoldbach/BinaryExceptional.lean` — Kernel-verified Lemma 6 dyadic counting (`dyadic_exceptional_bound`), global bound `binary_goldbach_exceptional_bound`, density-1 corollary `binary_goldbach_density_one`, and `#print axioms` audit.
- **[verify/](verify/)** — Independent computational verifiers:
  - `verify/verify_bounds.py` — 60-digit interval-arithmetic verification of every constant and inequality in `proof/weak_goldbach_proof.md`.
  - `verify/verify_binary_bounds.py` — 60-digit interval-arithmetic verification of every constant and inequality in `proof/binary_goldbach_exceptional_proof.md`.
  - `verify/verify_finite.cpp` — Multi-threaded C++17 direct verification of binary Goldbach for all even $4 \le E \le 10^9$ and deterministic 64-bit prime-ladder certification of Weak Goldbach for all odd $7 \le N \le 10^{12}$.
  - `verify/verify_ladder.py` + `verify/ladder_certs.json.gz` — Deterministic Pratt-certificate prime ladder (2,501 rungs, 13,197 unique certified primes) bridging $B = 4 \times 10^{18}$ (Oliveira e Silva, Herzog, Pardi 2014) to $N_0 = 10^{22}$.

## Reproducing All Checks

```bash
# 1. Lean 4 kernel build + axiom audit
cd lean && lake build

# 2. 60-digit interval-arithmetic audits of all analytic bounds
python3 verify/verify_bounds.py
python3 verify/verify_binary_bounds.py

# 3. Deterministic Pratt-certificate prime ladder from 4e18 to 1e22
python3 verify/verify_ladder.py 4000000000000000000 10000000000000000000000 verify/ladder_certs.json

# 4. Direct local C++ verification (binary Goldbach to 10^9, Weak Goldbach to 10^12)
g++ -O3 -std=c++17 -pthread verify/verify_finite.cpp -o verify/verify_finite
./verify/verify_finite 1000000000 1000000000000
```
