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
