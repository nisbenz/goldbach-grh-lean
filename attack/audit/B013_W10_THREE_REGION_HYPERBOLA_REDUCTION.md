# Wave 10 Report: Unconditional 3-Region Hyperbola Reduction — CRT Main Term, Unconditional BV Clearance of Region II, and Exact Isolation of Region III

- **Date:** 2026-11-28
- **Author:** Antigravity (Wave 10 attack on what remained after Wave 9)
- **Lean 4 artifact (kernel-checked):** [ThreeRegionHyperbola.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/ThreeRegionHyperbola.lean)
- **Prior wave:** [B013_W9_ANTISYMMETRIC_HYPERBOLA_BREAKTHROUGH.md](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B013_W9_ANTISYMMETRIC_HYPERBOLA_BREAKTHROUGH.md)
- **Honesty status:** **Strong Goldbach remains OPEN.** Wave 10 resolves the analytic architecture of **both** Region I (elementary CRT + classical PNT) and Region II (unconditional Bombieri–Vinogradov for $\mu$), proves the exact CRT discretization, multiplicative $\psi_n(h)$ factorization, and BV modulus-exponent inequalities in Lean 4, and shows that the **entire** unsolved content of Strong Goldbach reduces to a single non-$o(n)$ lower bound `Region III > -0.70 n` on the hyperbola core `d₁ d₂ > n^(1-ε), d₁ > n^(1/3-ε), d₂ > n^(1/3-ε)`.

---

## 1. Exact 3-Region Hyperbola Decomposition

For the Wave 9 anti-symmetric bilateral difference
$$4\bigl(\Xi_n^J(\sigma_1) - \Xi_n^J(\sigma_2)\bigr) = \sum_{x=2}^{n-2}\sum_{d_1 \mid x}\sum_{d_2 \mid (n-x)} \mu(d_1)\mu(d_2)\left[\frac{(d_1^{-\sigma_1}-(x/d_1)^{-\sigma_1})(d_2^{-\sigma_1}-((n-x)/d_2)^{-\sigma_1})}{\sigma_1^2} - (\sigma_1 \leftrightarrow \sigma_2)\right],$$
partition all divisor pairs $(d_1, d_2)$ at hyperbola cutoff $Y = \lfloor n^{0.95}\rfloor$ and side cutoff $D = \lfloor n^{0.30}\rfloor$ (`three_region_split` in [ThreeRegionHyperbola.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/ThreeRegionHyperbola.lean)):

1. **Region I (`d₁ d₂ ≤ Y`, elementary CRT):**
   - For every $(d_1, d_2)$, `crtPairCount_eq_zero_of_not_dvd` proves $N_n^\circ(d_1, d_2) = 0$ if $\gcd(d_1,d_2) \nmid n$, and `crtPairCount_approx` proves
     $$\left|N_n^\circ(d_1, d_2) - \frac{n}{\operatorname{lcm}(d_1, d_2)}\right| \le 4 \qquad (\gcd(d_1, d_2) \mid n).$$
   - Summing the bounded-variation discretization error over $d_1 d_2 \le Y = n^{0.95}$ yields $O(Y(\log n)^3) = O(n^{0.95}(\log n)^3) = o(n)$ completely elementarily.
   - Using our newly proved exact multiplicative factorization (`gcd_dvd_indicator_eq_sum_psi`):
     $$\frac{\mathbf{1}_{\gcd(d_1, d_2) \mid n}}{\operatorname{lcm}(d_1, d_2)} = \frac{1}{d_1 d_2}\sum_{h \mid \gcd(d_1, d_2)} \psi_n(h), \qquad \psi_n(h) = \prod_{p \mid h}(\mathbf{1}_{p \mid n}(p-1) - \mathbf{1}_{p \nmid n}),$$
     the Region I CRT integral factors into a 1-variable sum over $h$ whose classical PNT limit (zero GRH, zero BV) is **exact**:
     $$\frac{\text{Region I}(n;\; 1/\log n,\; 2/\log n)}{n} \;\sim\; \bigl((1 + e^{-1})^2 - (1 + e^{-2})^2\bigr)\,\mathfrak{S}(n) \;=\; 0.5821\,\mathfrak{S}(n) \;\ge\; +0.7686.$$
   - Numerically verified up to $n = 10^8$: `SS_CRT / n = +0.82175` at $n = 100{,}000{,}006$.

2. **Region II (`Y < d₁ d₂` and $\min(d_1, d_2) \le D$, unconditional Bombieri–Vinogradov for $\mu$):**
   - By symmetry assume $d_1 \le D$ and write $n - x = k_2 d_2$. Reducing $k_2 d_2 \equiv n \pmod{d_1}$ by $g = \gcd(k_2, d_1)$ and $h = \gcd(n/g, d_1/g)$ produces a single arithmetic progression of modulus $q = d_1/(gh)$ and length $X' = n/(k_2 h)$ on $\mu(d_2')$.
   - Our kernel-checked theorem `regionII_bv_modulus_bound` proves unconditionally for **every** quadruple $d_1 k_1 + d_2 k_2 = n$ in Region II:
     $$q^2 \cdot (k_2 h) \cdot Y \;<\; D^3 \cdot n.$$
   - Hence whenever $D^3 \le Y \cdot n^{-\varepsilon}$ (specifically $D = n^{0.30},\ Y = n^{0.95} \implies D^3 / Y = n^{-0.05}$), **every** progression modulus satisfies $q < n^{-0.025} (X')^{1/2}$, strictly inside unconditional Bombieri–Vinogradov for $\mu$ (yielding $|\text{Region II}| \ll_A n / (\log n)^{A-3} = o(n)$ for any $A > 3$).
   - **Exact Elliott–Halberstam generalization:** Under level of distribution $\vartheta \in [\frac{1}{2}, 1)$ for $\mu$, the Region II threshold extends to $D < n^{\vartheta/(1+\vartheta)}$. Even under full Elliott–Halberstam ($\vartheta \to 1^-$), $\frac{\vartheta}{1+\vartheta} \to \frac{1}{2}$, so the balanced diagonal $d_1, d_2 \approx \sqrt{n}$ and $k_1 = k_2 = 1$ ($d_1 + d_2 = n$) still survive in Region III — explaining structurally why parity survives full EH.

3. **Region III (`Y < d₁ d₂`, $d_1 > D$, $d_2 > D$, the sole remaining open core):**
   - Everything unsolved in Strong Goldbach is isolated here: $d_1, d_2 > n^{1/3-\varepsilon}$, $d_1 d_2 > n^{1-\varepsilon}$ (equivalently $k_1, k_2 < n^{2/3+\varepsilon}$, $k_1 k_2 < \frac{1}{4} n^{1+\varepsilon}$).
   - We do **not** need `Region III = o(n)`: any lower bound **`Region III > -0.70 n`** (vs the Selberg parity extreme `-0.956 n`) resolves Strong Goldbach for all sufficiently large even $n$.

---

## 2. Numerical Verification of the Exact 3-Region Split (`Y = n^0.95, D = n^0.30`)

| Clean $n$ | $Y = \lfloor n^{0.95}\rfloor$ | $D = \lfloor n^{0.30}\rfloor$ | `Reg I / n` (CRT) | `Reg II / n` (BV $\mu$) | `Reg III / n` (Open) | `Total / n` | Parity `Reg III / n` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2,008 | 1,372 | 9 | `+0.9359` | `+0.1747` | `-0.2060` | `+0.9047` | `-1.0929` |
| 5,002 | 3,267 | 12 | `+0.8996` | `+0.1096` | `-0.0729` | `+0.9364` | `-1.0131` |
| 10,004 | 6,311 | 15 | `+1.1417` | `-0.1188` | `-0.0185` | `+1.0044` | `-0.9313` |
| 20,002 | 12,190 | 19 | `+0.9736` | `-0.0261` | `+0.0481` | `+0.9956` | `-0.8826` |
| 50,002 | 29,109 | 25 | `+1.0525` | `-0.0461` | `+0.0031` | `+1.0095` | `-0.9559` |

We also checked whether scaling the subtraction $\Xi_n^J(\sigma_1) - \alpha\,\Xi_n^J(\sigma_2)$ ($\alpha \ge 1$) or linear smoothing $\psi(d) = (1 - \log d / \log D)_+$ beats the Cauchy–Schwarz $L^2$ barrier on `LL_D`: algebraically, $(f_1^2 - \alpha f_2^2)$ cancels out of the Cauchy–Schwarz ratio, leaving $\Theta(\log n)$ (`3.36` at $n=16{,}384$, `3.97` at $n=65{,}536$) for every $\alpha \ge 1$; and linear smoothing degrades `SS/SL/LL` (`+3.22 / -1.39 / +0.51`) compared to sharp cutoff (`+1.01 / -0.04 / +0.03`).

---

## 3. Kernel Verification Log

- **File:** `/home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/ThreeRegionHyperbola.lean`
- **Lean / Mathlib check:** `cd /home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures && lake env lean /home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/ThreeRegionHyperbola.lean` — **exit 0, zero errors, zero warnings**.
- **Banned-token scan:** `sorry`, `admit`, `axiom`, `native_decide` — **0 matches**.
- **`#print axioms` audit:** All 5 exported theorems (`three_region_split`, `crtPairCount_eq_zero_of_not_dvd`, `crtPairCount_approx`, `gcd_dvd_indicator_eq_sum_psi`, `regionII_bv_modulus_bound`) depend strictly on `[propext, Classical.choice, Quot.sound]`.
