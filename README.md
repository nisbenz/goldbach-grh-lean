> **Coordinated attack framework (2026-11-27, Waves 0–6).** A local, verifier-first attack system lives in
> [`attack/`](attack/) with the binding agent protocol at [`AGENTS.md`](AGENTS.md): a claim/blocker
> map, a lease desk, a kernel-checker (including a vendored Apache-2.0 checker with attribution),
> arXiv news monitoring, a dashboard, and a failure log. **Pointwise Strong (Binary) Goldbach remains
> OPEN** (including under ERH, ordinary prime EH, and $\mathrm{GL}_2$ Grand RH). As of Wave 6, the
> map records **22 checked claims**, **6 resolved blockers**, and **11 open blockers** (GitHub issues
> `#2`–`#12`) across 18 completed audit runs. See [`attack/map/blockers.json`](attack/map/blockers.json)
> and [`attack/failures.md`](attack/failures.md) for the exact state.

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
- **22 checked claims in [`attack/map/claims.json`](attack/map/claims.json):** includes H1 major-arc rational certificates, dyadic/prime-power bounds, plus **8 new Lean `v4.16.0` micro-lemmas** from Waves 1–2 (H3 centering & reflection energy, $L^p$ moment budget, weighted cube-root-rough prime detector, dyadic projector, $U_{16}$ reflection hole, and subcritical marked divisor).

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
  - *Analytic (ERH):* pointwise signed lower bound $\liminf_{2\mid N\to\infty} \mathcal{P}_N^\circ > -1/3$ on ultra-low zeros $|\gamma| < 2\log\log N$ at $Q = \lfloor N^{2/3}\rfloor$, **or**
  - *Sieve / Bilinear:* signed Type II on $[N^{0.43835}, \sqrt{N}]$ (under BV), **or** $c < 2$ on one central semiprime band (under prime EH), **or** uniform $L^{-2}$ reflected-prime Möbius saving / power-saving two-form cancellation of determinant $+N$ on the BV long-divisor tail $T_D$, **or**
  - *Ratios:* strict power saving $\vartheta < 1 - 2\eta$ in $2/2$ Dirichlet $L$-function ratios uniformly over $q \mid N$.
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
