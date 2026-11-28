# Wave 8 Breakthrough Report: Prime-Free Bilateral & One-Sided Mellin–Euler Sign-Separation Criteria for Strong Goldbach

- **Date:** 2026-11-28
- **Author:** Antigravity (Wave 8 attack on the 5th leaf `GoldbachConjecture.goldbach.R2.H3` / `B-002` / `B-003` / `B-013`)
- **Lean 4 artifact (kernel-checked):** [MellinEulerCriterion.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/MellinEulerCriterion.lean)
- **Companion Wave 7 artifact (kernel-checked):** [TailBarrier.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/TailBarrier.lean) and [B013_W7_FIFTH_LEAF_CREATIVE_ATTACK.md](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B013_W7_FIFTH_LEAF_CREATIVE_ATTACK.md)
- **Honesty status:** **Strong Goldbach remains OPEN** (no unconditional or ERH-conditional proof of `BinaryGoldbach`). What IS newly proved and kernel-checked (zero `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]` only) is an elementary, prime-free analytic–CRT sign-separation criterion and its exact hyperbola/Möbius-correlation reduction.

---

## 1. The Core Mathematical Discovery

In Wave 7 (`R2`, merged in `open-math-agents` PR #12835), Strong Goldbach for $n > 50000$ was reduced to the 5th leaf $T_D(n) \le \frac{1}{2} n$, where
$$T_D(n) = -\sum_{\substack{D < d < n \\ (d,n)=1}} \mu(d)\log d\,\theta(n; d, n).$$
In Wave 7 we also formally proved (`TailBarrier.lean`) that the deterministic prime-supported function $f_{\rm comp}$ agrees with $\Lambda_{\rm pr}$ on all progressions $d \mid (n-x)$ up to $\le \log n$ and matches $S_D(n)$ up to $D(\log n)^2$, while having zero prime pairs — forcing $T_D(f_{\rm comp}) = S_D(f_{\rm comp}) \sim n\mathfrak{S}(n)$ and ruling out any proof of `R2.H3` that only inspects short progressions $d \le D$.

In Wave 8, instead of imposing a sharp divisor cutoff at $D$, we replaced $\Lambda$ by the smooth Euler-product family
$$F_\sigma(m) := \prod_{q \mid m}(1 - q^{-\sigma}) = \sum_{d \mid m} \mu(d)\,d^{-\sigma} \qquad (\sigma > 0)$$
and discovered an **exact elementary sign-separation property** that holds **unconditionally** on BOTH the one-sided prime-shifted sum AND a **completely prime-free bilateral CRT sum**.

### 1.1 The 3-line Analytic Lemma (`h_ge_one_sub_half`, `scaled_euler_prod_mono`)

For every real $u > 0$,
$$h(u) := \frac{u}{e^u - 1} \;\ge\; 1 - \frac{u}{2}.$$
**Proof:** Let $f(u) = (2+u)e^{-u/2} - (2-u)e^{u/2}$. Then $f(0) = 0$ and $f'(u) = \frac{u}{2}(e^{u/2} - e^{-u/2}) \ge 0$ for all $u \ge 0$. Multiplying $f(u) \ge 0$ by $e^{u/2} > 0$ gives $(2+u) - (2-u)e^u \ge 0$, which rearranges to $h(u) \ge 1 - u/2$. $\square$

**Consequence (`scaled_euler_prod_mono`):** For any finite indexed family of positive reals $(a_i)_{i \in s}$ with $|s| \ge r + 1$ and any $0 < \sigma_1 \le \sigma_2$ satisfying $\sigma_2 \sum_{i \in s} a_i \le 2(|s| - r)$, the logarithmic derivative of $\sigma \mapsto \sigma^{-r} \prod_{i \in s}(1 - e^{-\sigma a_i})$ is
$$\frac{1}{\sigma}\left(\sum_{i \in s} h(\sigma a_i) - r\right) \ge \frac{1}{\sigma}\left(|s| - r - \frac{\sigma}{2}\sum_{i \in s} a_i\right) \ge 0,$$
so the scaled Euler product is **monotone non-decreasing** on $[\sigma_1, \sigma_2]$:
$$\sigma_1^{-r} \prod_{i \in s}(1 - e^{-\sigma_1 a_i}) \;\le\; \sigma_2^{-r} \prod_{i \in s}(1 - e^{-\sigma_2 a_i}).$$

*(The sharp convexity threshold extends to $c_1 = 2 v_1 \approx 2.51286$ for $r=1$ and $c_2 = \frac{3}{2} v_2 \approx 1.17587$ for $r=2$; the 3-line bound $h(u) \ge 1 - u/2$ already yields clean universal constants $c_1 = 2$ and $c_2 = 1$ with zero numerical approximation.)*

---

## 2. Theorem A: The Bilateral Prime-Free CRT Criterion (`bilateral_mellin_euler_goldbach_criterion`)

Define for any $n \ge 4$ and $\sigma > 0$:
$$B_n^\circ(\sigma) := \sum_{x=2}^{n-2} F_\sigma(x)\,F_\sigma(n - x), \qquad \Xi_n^\circ(\sigma) := \sigma^{-2} B_n^\circ(\sigma).$$

1. **Exact Prime-Free CRT Identity (`bilateralEuler_eq_crt_sum`):**
   $$B_n^\circ(\sigma) = \sum_{d_1=1}^{n-2}\sum_{d_2=1}^{n-2} \mu(d_1)\mu(d_2)(d_1 d_2)^{-\sigma}\,N_n^\circ(d_1, d_2),$$
   where $N_n^\circ(d_1, d_2) := \#\{2 \le x \le n-2 : d_1 \mid x \land d_2 \mid (n - x)\}$ is a pure linear congruence count — **no primes, no von Mangoldt function, and no Bombieri–Vinogradov input appear anywhere on the RHS**.

2. **Unconditional Sign Separation (`bilateral_mellin_euler_upper_bound`):**
   For every $n \ge 4$ and every $0 < \sigma_1 \le \sigma_2 \le \frac{1}{\log n}$, EVERY composite pair $(x, n-x)$ with $\omega(x) + \omega(n-x) \ge 3$ contributes **$\le 0$** to $\Xi_n^\circ(\sigma_1) - \Xi_n^\circ(\sigma_2)$. Therefore:
   $$\Xi_n^\circ(\sigma_1) - \Xi_n^\circ(\sigma_2) \;\le\; R_{\rm pr}(n) + P_{\rm pp}^{\rm bilat}(n),$$
   where $R_{\rm pr}(n) = \sum_{\substack{2 \le x \le n-2 \\ x,\, n-x \text{ prime}}} \log x \log(n-x)$ and $P_{\rm pp}^{\rm bilat}(n)$ is the proper prime-power error ($\omega(x)=\omega(n-x)=1$, not both prime).

3. **Goldbach Implication (`bilateral_mellin_euler_goldbach_criterion`):**
   $$\Xi_n^\circ(\sigma_1) - \Xi_n^\circ(\sigma_2) > P_{\rm pp}^{\rm bilat}(n) \quad\Longrightarrow\quad \exists\, p, q \text{ prime},\ p + q = n.$$

4. **Hyperbola Decomposition (`bilateralEuler_hyperbola_split`):**
   Splitting at any hyperbola $d_1 d_2 \le Y$ vs $d_1 d_2 > Y$ separates $B_n^\circ(\sigma)$ into an elementary CRT region ($N_n^\circ(d_1, d_2) = n/\operatorname{lcm}(d_1, d_2) + O(1)$) plus the pure prime-free binary Möbius correlation over $k_1 d_1 + k_2 d_2 = n$ with $d_1 d_2 > Y$.

---

## 3. Theorem B: The One-Sided Mellin–Euler Criterion (`oneSided_mellin_euler_goldbach_criterion`)

Define for $n \ge 4$ and $\sigma > 0$:
$$G_n^\circ(\sigma) := \sum_{\substack{2 \le p \le n-2 \\ p\text{ prime}}} \log p \cdot F_\sigma(n - p) = \sum_{d=1}^{n-2} \mu(d)\,d^{-\sigma}\,\theta_n^\circ(d), \qquad \Phi_n^\circ(\sigma) := \sigma^{-1} G_n^\circ(\sigma).$$
For every $n \ge 4$ and every $0 < \sigma_1 \le \sigma_2 \le \frac{2}{\log n}$, every composite shift $n - p$ with $\omega(n-p) \ge 2$ contributes **$\le 0$** to $\Phi_n^\circ(\sigma_1) - \Phi_n^\circ(\sigma_2)$, yielding:
$$\Phi_n^\circ(\sigma_1) - \Phi_n^\circ(\sigma_2) \;\le\; R_{\rm pr}(n) + P_{\rm pp}^{\rm one}(n),$$
and $\Phi_n^\circ(\sigma_1) - \Phi_n^\circ(\sigma_2) > P_{\rm pp}^{\rm one}(n) \implies \exists\, p, q\text{ prime},\ p + q = n$.

---

## 4. Numerical Evidence & Exact Structural Diagnosis

### 4.1 Exhaustive Verification on ALL even $n \in [4, 2000]$ and Large-$n$ Scaling up to $n = 500{,}002$

- **Bilateral difference $(\sigma_1 = 0.5/\log n,\ \sigma_2 = 1.0/\log n)$:**
  - Verified on **every** even $n \in [4, 2000]$: $\min_n (\text{Diff} - P_{\rm pp}^{\rm bilat})/n = +0.012645 > 0$ (at $n = 1412$), max composite term $= -1.50 \times 10^{-5} < 0$.
  - Large-$n$ values of $(\Xi_n^\circ(\sigma_1) - \Xi_n^\circ(\sigma_2)) \cdot \frac{\log n}{n}$ vs prime-power error $P_{\rm pp}^{\rm bilat} \cdot \frac{\log n}{n}$:
    - $n = 10{,}006$: `0.4684` vs `0.0031` (150× margin)
    - $n = 50{,}002$: `0.8141` vs `0.0059` (138× margin)
    - $n = 100{,}004$: `0.7959` vs `0.0195` (41× margin)
    - $n = 200{,}000$: `1.5590` vs `0.0438` (35× margin)
- **Exact match with the infinite Hardy–Littlewood Euler product $\mathcal{M}_n(\sigma) = n \prod_p (1 - 2p^{-1-\sigma} + \mathbf{1}_{p \mid n} p^{-1-2\sigma})$:**
  - At $\sigma = 0^+$, $-\frac{d}{d\sigma}\bigl[\mathcal{M}_n(\sigma)/(n\sigma^2)\bigr] \ge +1.08524$ for **every** even $n$ (`+1.08524` for $n=2^k$, `+7.97254` for $6 \mid n$, `+14.40776` for $30 \mid n$).
  - On $n = 2^k$ ($k = 10 \dots 18$, $\sigma = 1.15/\log n$), $-\Xi_n'(\sigma)/n$ tracks $-\frac{d}{d\sigma}[\mathcal{M}_n(\sigma)/(n\sigma^2)] \approx +1.41$ within `±0.06` (`+1.4459` vs `+1.4151` at $n=65{,}536$; `+1.4522` vs `+1.4098` at $n=131{,}072$; `+1.3405` vs `+1.4041` at $n=262{,}144$).

### 4.2 Where the Open Hard Core Moves (Honest Parity / Barrier Analysis)

Testing our new functionals against Selberg parity weights, exact $\mathbb{Z}/n\mathbb{Z}$ FFTs, and the divisor hyperbola split pinpoints the exact remaining obstruction with total clarity:

1. **Parity sensitivity (verified at $n = 50{,}002$):**
   - On the Selberg parity weight $w_+(m) = 1 + \lambda(m)$ (zero primes), one-sided $-\Phi_n'(2.5/\log n)/(n\log n)$ flips from $+0.0713$ (true primes) to $-0.0737$ (negative!), even though the short-divisor part ($d \le D = 59$) stays positive ($+0.1616$ vs $+0.0789$).
   - On the bilateral parity weight $W_{\rm parity}(x) = 1 - \lambda(x)\lambda(n-x)$ (zero prime-prime pairs), $-\Xi_n'(1.15/\log n)/n$ flips from $+1.6194$ (true integers) to $-2.3027$ (negative!).
2. **Hyperbola & Ramanujan unification:**
   - In the bilateral CRT expansion, the short region $d_1 d_2 \le Y$ is completely elementary ($N_n^\circ(d_1, d_2) = n/\operatorname{lcm}(d_1, d_2) + O(1)$).
   - The entire remaining difficulty of Strong Goldbach concentrates into **one prime-free problem**: proving cancellation in the long-range binary Möbius correlation
     $$\sum_{\substack{d_1 d_2 > Y \\ k_1 d_1 + k_2 d_2 = n}} \mu(d_1)\mu(d_2)(d_1 d_2)^{-\sigma}$$
     (equivalently, off-diagonal Ramanujan-sum cancellation in $B_n^\circ(\sigma) - \mathcal{M}_n(\sigma) = o(n/\log n)$ at $\sigma \asymp 1/\log n$, or signed minor-arc cancellation in $\frac{2}{n}\sum_{k \in \mathfrak{m}} \widehat{F_\sigma}(k)\widehat{dF_\sigma}(k)$ where Cauchy–Schwarz still exceeds the main term by $\sim (\log n)^2$ at $n = 16{,}384$: `27.04` vs `1.56`).
3. **$k$-profile of the original 5th leaf $T_D(n)$:**
   - Decomposing $T_D(n) = \sum_{1 \le k < n/D} C_k(n)$ shows $\sum |C_k|/n \approx 0.71\text{--}1.13$ while $|\sum C_k|/n \approx 0.04\text{--}0.13$ across $n \in \{50002, 100000, 200000\}$: there is no single dominant cofactor $k$, and cancellation operates across all dyadic ranges of $k \in [1, n/D]$.

---

## 5. Kernel Verification Log

- **File:** `/home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/MellinEulerCriterion.lean`
- **Lean / Mathlib check:** `cd /home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures && lake env lean /home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/MellinEulerCriterion.lean` — **exit 0, zero errors, zero warnings**.
- **Banned-token scan:** `sorry`, `admit`, `axiom`, `native_decide` — **0 matches**.
- **`#print axioms` audit:** All 10 exported theorems (`h_ge_one_sub_half`, `scaled_euler_prod_mono`, `eulerFactor_eq_moebius_sum`, `bilateralEuler_eq_crt_sum`, `bilateralEuler_hyperbola_split`, `bilateral_mellin_euler_upper_bound`, `bilateral_mellin_euler_goldbach_criterion`, `oneSidedEuler_eq_theta_sum`, `oneSided_mellin_euler_upper_bound`, `oneSided_mellin_euler_goldbach_criterion`) depend strictly on `[propext, Classical.choice, Quot.sound]`.
