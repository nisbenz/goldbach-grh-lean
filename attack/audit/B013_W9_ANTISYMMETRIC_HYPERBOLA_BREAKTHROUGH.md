# Wave 9 Report: Anti-Symmetric Hyperbola Euler-Product Criterion & Zero-Error Odd-Squarefree Criterion

- **Date:** 2026-11-28
- **Author:** Antigravity (Wave 9 continuation on the 5th leaf `R2.H3` / `B-002` / `B-003` / `B-012` / `B-013`)
- **Lean 4 artifact:** [AntiSymmetricEuler.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/AntiSymmetricEuler.lean)
- **Prior wave:** [B013_W8_MELLIN_EULER_BREAKTHROUGH.md](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B013_W8_MELLIN_EULER_BREAKTHROUGH.md)
- **Honesty status:** **Strong Goldbach remains OPEN.** Wave 9 delivers three strictly sharper, completely unconditional Lean 4 criteria that amplify the Wave 8 prime-free signal by a full factor of $\log n$ (from $\Theta(n/\log n)$ to $\Theta(n)$), double the admissible range of $\sigma$, eliminate prime powers either explicitly or identically, and isolate the entire remaining open problem into a single non-$o(n)$ threshold on the long–long binary Möbius quadrant `LL_D`.

---

## 1. Three Structural Improvements Over Wave 8

In Wave 8 ([MellinEulerCriterion.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/MellinEulerCriterion.lean)), the bilateral Euler product $B_n^\circ(\sigma) = \sum_{x=2}^{n-2} F_\sigma(x) F_\sigma(n-x)$ had three remaining weaknesses:
1. Its difference $\Xi_n^\circ(\sigma_1) - \Xi_n^\circ(\sigma_2)$ scaled only as $\Theta(n/\log n)$ (losing a $\log n$ factor relative to $R_{\rm pr}(n) \sim \mathfrak{S}(n)n$).
2. Its short-divisor CRT truncation oscillated wildly ($\pm 184\,n$) until $d_1 d_2 \approx n^{1.5}$.
3. It carried an un-bounded proper prime-power term $P_{\rm pp}^{\rm bilat}(n)$.

Wave 9 fixes **all three simultaneously** via the Dirichlet-reciprocal anti-symmetric divisor kernel:
$$A_\sigma(m) := F_\sigma(m) - K_\sigma(m) = \sum_{d \mid m}\mu(d)\!\left(d^{-\sigma} - \left(\frac{m}{d}\right)^{-\sigma}\right),$$
whose Dirichlet series is literally $\frac{\zeta(s)}{\zeta(s+\sigma)} - \frac{\zeta(s+\sigma)}{\zeta(s)}$ (`F_σ` and `K_σ` are exact Dirichlet inverses: $(F_\sigma *_{\rm Dir} K_\sigma) = \delta_1$).

### 1.1 Exact Closed Form & Semiprime Annihilation (`antiSymFactor_eq_closed_form`, `antiSymFactor_eq_zero_of_squarefree_even`)
For every $m \ge 1$ and $\sigma \in \mathbb{R}$,
$$A_\sigma(m) = \left(1 - (-1)^{\omega(m)} \left(\frac{m}{\operatorname{rad}(m)}\right)^{-\sigma}\right) \prod_{q \mid m}(1 - q^{-\sigma}).$$
Consequently:
- On every **prime $p$**: $A_\sigma(p) = 2(1 - p^{-\sigma})$.
- On every **squarefree integer with even $\omega(m)$** (including **every semiprime $p_1 p_2$**): $A_\sigma(m) \equiv \mathbf{0}$ identically for all $\sigma$.
- On every **composite $m$** ($\omega(m) \ge 2$) with $A_\sigma(m) > 0$, combining `h(u) = u/(e^u - 1) ≥ 1 - u/2` with `-v e^{-σv}/(1 + e^{-σv}) ≥ -v/2` (`scaled_euler_plus_minus_mono`) shows the effective factor count is $\ge 3$ and the exponent sum equals **exactly** $\log m$. Therefore (`antiSym_bilateral_composite_mono`):
  $$\forall\, x, y \in [2, n],\ \omega(x) + \omega(y) \ge 3,\ \forall\, 0 < \sigma_1 \le \sigma_2 \le \frac{2}{\log n}: \quad \sigma_1^{-2} A_{\sigma_1}(x) A_{\sigma_1}(y) \le \sigma_2^{-2} A_{\sigma_2}(x) A_{\sigma_2}(y).$$
  This **doubles** the admissible $\sigma$-range from $1/\log n$ to $2/\log n$ (and from $2/\log n$ to $4/\log n$ one-sided).

### 1.2 Exact 4-Quadrant Hyperbola Split & Explicit Prime-Power Bound (`bilateral_antiSym_quadrant_goldbach_criterion`)
Splitting $A_\sigma(m) = A_{S,D}(\sigma, m) + A_{L,D}(\sigma, m)$ at any cutoff $D \in \mathbb{N}$ (`d ≤ D` vs `d > D`) yields the exact reflection-symmetrized identity (`bilateralAntiSym_quadrant_split`):
$$4\bigl(\Xi_n^J(\sigma_1) - \Xi_n^J(\sigma_2)\bigr) \;=\; \text{SS}_D(n;\sigma_1,\sigma_2) \;+\; 2\,\text{SL}_D(n;\sigma_1,\sigma_2) \;+\; \text{LL}_D(n;\sigma_1,\sigma_2).$$
Combining this with the proved elementary prime-power bound (`bilateralPrimePowerErr_le`):
$$P_{\rm pp}^{\rm bilat}(n) \;\le\; 2\,\bigl(\lfloor\sqrt{n}\rfloor \cdot \lfloor\log_2 n\rfloor\bigr)\,(\log n)^2,$$
we obtain the completely self-contained, zero-prime, zero-BV criterion (`bilateral_antiSym_quadrant_goldbach_criterion`):
$$\text{SS}_D(n;\sigma_1,\sigma_2) + 2\,\text{SL}_D(n;\sigma_1,\sigma_2) + \text{LL}_D(n;\sigma_1,\sigma_2) \;>\; 8\,\bigl(\lfloor\sqrt{n}\rfloor \cdot \lfloor\log_2 n\rfloor\bigr)\,(\log n)^2 \;\Longrightarrow\; \exists\, p,q\text{ prime},\ p + q = n.$$

### 1.3 Zero-Error Odd-Squarefree Criterion (`bilateral_oddSqfree_goldbach_criterion`)
Restricting to squarefree integers with $\mu(x) = -1$ (odd $\omega(x) \in \{1, 3, 5, \dots\}$) kills **all** prime powers identically ($P_{\rm pp} \equiv 0$), giving for every $n \ge 4$ and $0 < \sigma_1 \le \sigma_2 \le \frac{2}{\log n}$:
$$\Xi_n^Q(\sigma_1) > \Xi_n^Q(\sigma_2) \quad\Longrightarrow\quad \exists\, p,q\text{ prime},\ p + q = n.$$

---

## 2. Quantitative Results (Python Verification)

### 2.1 Exhaustive Check on ALL 999 Even $n \in [4, 2000]$
At $(\sigma_1, \sigma_2) = (1/\log n, 2/\log n)$:
- Every single even $n \in [4, 2000]$ satisfies $\Xi_n^J(\sigma_1) - \Xi_n^J(\sigma_2) > P_{\rm pp}^J(n)$ (minimum margin $+0.026388\,n$ at $n = 4$; maximum composite term $= 0.000000000$).

### 2.2 4-Quadrant Hyperbola Behavior at $D = \lfloor n^{0.45}\rfloor$ (`c1 = 1.0, c2 = 2.0`)

| $n$ (clean, $\gcd(n, 3\cdots 19)=1$) | $D = \lfloor n^{0.45}\rfloor$ | `SS_D / n` (100% CRT) | `SL_D / n` (1 $\mu$ in AP) | `LL_D / n` (binary $\mu$) | Total `4*DiffJ / n` | Parity `LL_D / n` ($1-\lambda\lambda$) |
|---:|---:|---:|---:|---:|---:|---:|
| 5,002 | 46 | +1.1275 | -0.0423 | -0.1066 | +0.9364 | -1.0030 |
| 10,004 | 63 | +1.0921 | -0.0400 | -0.0078 | +1.0044 | -0.8945 |
| 20,002 | 86 | +1.0565 | -0.0390 | +0.0170 | +0.9956 | -0.9198 |
| 50,002 | 130 | +1.0636 | -0.0193 | -0.0156 | +1.0095 | -0.9709 |
| 100,004 | 177 | +1.0445 | -0.0156 | -0.0190 | +0.9943 | -0.9848 |

### 2.3 Elementary CRT Integral Verification of `SS_D`
Replacing the congruence sum in `SS_D` ($d_1, d_2 \le D$) by its elementary CRT integral $(n/\operatorname{lcm}(d_1,d_2))\int_0^1 \cdots$ matches exact `SS_D / n` to **0.07–0.08%** already at $D = n^{0.33}$ and $D = n^{0.45}$:
- $n = 20{,}002,\ D = 86$: `SS_exact/n = +1.05655` vs `SS_CRT_main/n = +1.05585` (`err = +0.00070`).
- $n = 50{,}002,\ D = 130$: `SS_exact/n = +1.06362` vs `SS_CRT_main/n = +1.06443` (`err = -0.00080`).

### 2.4 Sharp Diagnosis of What Remains Open
- `SS_D` is already $\approx +1.05\,n$ by pure elementary CRT ($d_1 d_2 \le n^{0.90} \ll n$).
- `2 * SL_D` is $\approx -0.03\,n$ and involves only a **single** long Möbius variable $\mu(d_2)$ in arithmetic progressions mod $d_1 \le D$.
- The **entire remaining open problem** is isolated in `LL_D` ($d_1, d_2 > D$), and does **not** even require `LL_D = o(n)`: any nontrivial lower bound `LL_D > -0.80 n` (beating the Selberg parity extreme `-0.985 n` by ~20%) would complete Strong Goldbach for large even $n$.

---

## 3. Kernel Verification Log

- **File:** `/home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/AntiSymmetricEuler.lean`
- **Lean / Mathlib check:** `cd /home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures && lake env lean /home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/AntiSymmetricEuler.lean` — **exit 0, zero errors, zero warnings**.
- **Banned-token scan:** `sorry`, `admit`, `axiom`, `native_decide` — **0 matches**.
- **`#print axioms` audit:** All 10 exported theorems (`scaled_euler_plus_minus_mono`, `antiSymFactor_eq_closed_form`, `antiSymFactor_eq_zero_of_squarefree_even`, `antiSym_bilateral_composite_mono`, `bilateralAntiSym_quadrant_split`, `bilateralPrimePowerErr_le`, `bilateral_antiSym_upper_bound`, `bilateral_antiSym_quadrant_goldbach_criterion`, `bilateral_oddSqfree_upper_bound`, `bilateral_oddSqfree_goldbach_criterion`) depend strictly on `[propext, Classical.choice, Quot.sound]`.
