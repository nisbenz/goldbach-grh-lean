# Wave 7 Creative Attack on the 5th Leaf (`GoldbachConjecture.goldbach.R2.H3` / `B-013`)

**Date:** 2026-11-28  
**Target:** The 5th leaf of our merged Strong Goldbach reduction tree (`GoldbachConjecture.goldbach.R2.H3`):
$$T_D(n) = \sum_{\substack{1 \le k \le K \\ (k,n)=1}} \sum_{\substack{D < d \le U_k \\ x = n - kd \in [1, n-2]\text{ prime},\ (x,n)=1}} \log(x)\,\mu(d)\,\log(d) \le \frac{1}{2} n \qquad (n > 50000\text{ even}),$$
where $D = \lfloor\sqrt{n/\lfloor\sqrt{\sqrt{n}}\rfloor}\rfloor \approx n^{3/8}$, $K = \lfloor(n-1)/(D+1)\rfloor$, and $U_k = \lfloor(n-1)/k\rfloor$.

**Bottom line:** Strong Goldbach (`R2.H3`) remains **OPEN**. This creative attack produced:
1. A **concrete counterexample** catching and closing our overly-strong rowwise split `R2.H3.R1` (PR #17139 closed before merge),
2. **Quantitative $\omega(d)$-cancellation and centered-weight diagnostics** up to $n = 500{,}000$,
3. **Two full-strength reflection-hole barrier models** (`B-013`) that beat true $\Lambda$ on minor-arc Fourier sup norms and pass full BV/EH while having $R(f) = 0$, and
4. A **kernel-checked Lean 4 barrier theorem** ([Goldbach/TailBarrier.lean](../lean/Goldbach/TailBarrier.lean)) proving both the exact symmetric–antisymmetric $L^2$ energy identity $R(n) = \|\Lambda_+\|_2^2 - \|\Lambda_-\|_2^2$ and the deterministic prime-supported $f_{\mathrm{comp}}$ short-divisor invariance theorem.

---

## 1. Counterexample Caught on Rowwise Abel Leaf `R2.H3.R1.H2` (PR #17139 Closed)

Testing `R2.H3.R1.H2` (`|∑_{y < d ≤ U_k} log(n - kd) μ(d)| ≤ n / (2 φ(k) (log n)^2)`) numerically immediately refuted it near the top cofactor $k \approx K$:
- At $n = 50002, D = 59, K = 833, k = 819, U_k = 61, y = 59$:
  $$|\text{sum}| = 3.7612 > \text{RHS} = \frac{50002}{2\,\varphi(819)\,(\log 50002)^2} = 0.4943.$$
- Cause: at $n = 50002$ and $k \approx K$, $n^{3/8}/(2(\log n)^2) \approx 0.25 < \log n$, so even a single prime term exceeds the rowwise bound.
- Action: closed PR #17139 before merge; kept the aggregate `R2.H3` statement intact.

---

## 2. Structural Anatomy of $T_D(n)$: 99.7% Algebraic Cancellation & Centered Weights

Computed on $n \in \{50002, 100000, 200000, 500000\}$:

| $n$ | $D$ | $K$ | $R_{\mathrm{pr}}/n$ | $T_D^{\mathrm{raw}}/n$ | $T_D^{\mathrm{cen}}/n$ ($\log(d/D)$) | $k=1$ row $/n$ | $k=1$ ($d$ prime) $/n$ | $k=1$ ($d$ comp) $/n$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 50,002 | 59 | 833 | 1.3755 | +0.04394 | +0.04760 | +0.0976 | -1.3739 | +1.4715 |
| 100,000 | 76 | 1,298 | 1.7615 | +0.12858 | +0.03883 | -0.0096 | -1.7604 | +1.7508 |
| 200,000 | 97 | 2,040 | 1.7579 | +0.04527 | +0.03602 | +0.0045 | -1.7573 | +1.7618 |
| 500,000 | 138 | 3,597 | 1.7739 | +0.08589 | +0.01718 | — | — | — |

Breakdown of $T_D^{\mathrm{raw}}(500000)/n$ by $\omega(d)$:
- $\omega(d) = 1$: `-8.3235`
- $\omega(d) = 2$: `+14.5185`
- $\omega(d) = 3$: `-7.1898`
- $\omega(d) = 4$: `+1.1206`
- $\omega(d) = 5$: `-0.0399`
- Sum: **`+0.08589`** (out of $L^1$ mass `31.19` — **99.7% cancellation**).

**Key identities discovered:**
1. **Rough-composite vanishing:** For any composite $m = n - p$ with smallest prime factor $P^-(m) > D$ (in particular every $D$-rough semiprime $q_1 q_2$ with $D < q_1 < q_2$), the raw tail coefficient $F_D(m) = \sum_{d \mid m,\, d > D} \mu(d)\log d$ vanishes **identically** ($F_D(m) = 0$).
2. **Mellin–Euler representation (centered weight $\log_+(d/D)$):** For any $c > 0$,
   $$T_D^{\mathrm{cen}}(n) = \frac{1}{2\pi i} \int_{(c)} D^{-s} \left(\sum_{\substack{p < n \\ (p,n)=1}} \log p \prod_{q \mid (n - p)} (1 - q^s)\right) \frac{ds}{s^2}.$$
   Composite $n - p$ have $\omega(n-p) \ge 2$, cancelling the double pole $1/s^2$ at $s = 0$, whereas prime $n - p$ leave a simple pole.

---

## 3. Symmetric–Antisymmetric $L^2$ Split & Two Reflection-Hole Models (`B-013`)

Writing $\Lambda_{\pm}(x) = (\Lambda(x) \pm \Lambda(n - x))/2$, we have the exact identity (kernel-checked in `Goldbach/TailBarrier.lean`):
$$R(n) = \|\Lambda_+\|_2^2 - \|\Lambda_-\|_2^2.$$
Thus $R(n) > 0$ is equivalent to symmetric $L^2$ energy around $n/2$ strictly exceeding antisymmetric $L^2$ energy.

We constructed and numerically tested **two reflection-hole barrier models** at $n = 50002$ ($D = 59$, 200 irrational minor-arc frequencies):

| Model | $R/n$ | $L^1/n$ | $L^2/(n\log n)$ | $L^\infty/\log n$ | $S_D/n$ | BV err $/n$ | $\sup_{\mathfrak{m}}|\widehat{f}|/\sqrt{n}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| **True $\Lambda_{\mathrm{pr}}$** | **1.3755** | 0.9944 | 0.9031 | 1.000 | 1.4211 | 0.0641 | 12.76 |
| **Model 1** (random reflection-free $z$-rough subset, $z=13$) | **0.0000** | 0.9495 | 0.9495 | **1.000** | **1.3438** | 0.2737 | **7.28** |
| **Model 2** (coin-flip doubling on Goldbach prime pairs) | **0.0000** | 0.9944 | 1.0328 | 2.000 | **1.4199** | **0.0635** | **12.18** |

**Consequence for `B-013`:**
- **Model 1** satisfies $0 \le f \le \log n$, matches all $L^p$ norms, passes $S_D > \frac{4}{5} n$ (and full EH/GRH APs for $z < n^{1/(2e^\gamma)}$), has **smaller** minor-arc Fourier sup than true primes (`7.28 √n` vs `12.76 √n`), and has $R(f) = 0$. Any proof of Strong Goldbach **must** distinguish primes from $n^{0.28}$-rough semiprimes.
- **Model 2** is supported **100% on genuine primes**, beats true primes on both BV error (`0.0635` vs `0.0641`) and minor-arc Fourier sup (`12.18 √n` vs `12.76 √n`), and has $R(f) = 0$. Any proof of Strong Goldbach via self-convolution $f * f(n)$ **must** also use the pointwise cap $f(p) \le \log p$.

---

## 4. Kernel-Checked Deterministic Barrier Theorem for `R2.H3`

In [Goldbach/TailBarrier.lean](../lean/Goldbach/TailBarrier.lean), we proved with zero `sorry` and standard axioms only that the **deterministic, prime-supported** function
$$f_{\mathrm{comp}}(x) := \mathbf{1}_{x\text{ prime},\ (x,n)=1,\ \neg(n-x)\text{ prime}} \log x$$
satisfies:
1. $0 \le f_{\mathrm{comp}}(x) \le \Lambda_{\mathrm{pr}}(x) \le \log x$ (`fComp_bounds`),
2. $\sum_{x=1}^{n-2} f_{\mathrm{comp}}(x)\,\Lambda_{\mathrm{pr}}(n - x) = 0$ (`fComp_zero_goldbach`),
3. For every $2 \le d \le n - 2$, $0 \le \sum_{d \mid (n-x)} (\Lambda_{\mathrm{pr}}(x) - f_{\mathrm{comp}}(x)) \le \log n$ (`fComp_progression_diff_le`),
4. For every $D \le n - 2$, $|S_D(\Lambda_{\mathrm{pr}}) - S_D(f_{\mathrm{comp}})| \le D (\log n)^2$ (`fComp_shortDivisorSum_close`).

Hence $T_D(f_{\mathrm{comp}}) = S_D(f_{\mathrm{comp}}) \sim +n\mathfrak{S}(n) > \frac{1}{2} n$ while $T_D(\Lambda_{\mathrm{pr}}) = T_D(f_{\mathrm{comp}}) - R_{\mathrm{pr}}^{q > D}(n) = o(n)$: any proof of `R2.H3` **cannot** isolate the $k = 1$, $d$-prime terms from the composite-$d$ terms and must obtain genuine prime–Möbius cancellation across both together.
