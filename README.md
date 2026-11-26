> **Coordinated attack framework (2026-11-27).** A local, verifier-first attack system now lives in
> [`attack/`](attack/) with the binding agent protocol at [`AGENTS.md`](AGENTS.md): a claim/blocker
> map, a lease desk, a kernel-checker (including a vendored Apache-2.0 checker with attribution),
> arXiv news monitoring, a dashboard, and a failure log. Binary Goldbach is still OPEN; the
> framework records 11 checker-verified micro-results and 11 open blockers. See AGENTS.md §9 for
> the blocker handoff.

# goldbach-grh-lean

Explicit GRH-conditional proofs, `sorry`-free Lean 4 (`v4.16.0` + Mathlib) formalizations, and independent 60-digit interval-arithmetic & computational verifiers for:

1. **Weak (Ternary) Goldbach Conjecture under GRH:** Every odd integer $N \ge 7$ is the sum of three primes.
2. **Binary (Strong) Goldbach Exceptional-Set Theorem under GRH:** For every $X \ge 4$, the number $E(X)$ of even integers in $[4, X]$ that are *not* sums of two primes satisfies
   $$E(X) \le 2{,}000{,}000\,\sqrt{X}\,(\log X)^3,$$
   and hence $E(X)/X \to 0$ as $X \to \infty$ (almost all even integers are sums of two primes). *(Note: pointwise Strong Goldbach for all even $N > 2$ remains open even under GRH.)*

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
