# Wave 13 Report: Boundary-Damped Anti-Symmetric Euler Kernel $\widetilde{A}_{n,\sigma}$ — Eliminating the $k_1 = k_2 = 1$ Binary-Chowla $(\log n)^2$ Blowup

- **Date:** 2026-11-28
- **Author:** Antigravity (Wave 13 `/goal` push on the Region III boundary)
- **Lean 4 artifact (kernel-checked):** [DampedBoundaryEuler.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/DampedBoundaryEuler.lean)
- **Prior wave:** [B013_W12_KLOOSTERMAN_BETTIN_CHANDEE_CLEARING.md](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B013_W12_KLOOSTERMAN_BETTIN_CHANDEE_CLEARING.md)
- **Honesty status:** **Strong Goldbach remains OPEN.** Wave 13 eliminates the $(\log n)^2$ binary-Chowla parity blowup at $k_1 = k_2 = 1$ ($\max(\alpha_1, \alpha_2) \to 1$) that blocked optimal general-coefficient Kloosterman cancellation in Wave 12, reducing the $k_1 = k_2 = 1$ slice by 250× (from `-6.8639 n` to `-0.0274 n` at $n = 50{,}002$) and evacuating 100% of the negative parity mass out of $\max(\alpha_1, \alpha_2) > 0.90$ into the power-saving Kloosterman interior $\max(\alpha_1, \alpha_2) \in [0.70, 0.90]$.

---

## 1. The Boundary-Damped Kernel $\widetilde{A}_{n,\sigma}$

In Wave 12 (`KloostermanMaster.lean`), we proved that optimal general-coefficient Kloosterman cancellation clears every dyadic box in Region III with $\max(\alpha_1, \alpha_2) < 1$, and that the sole boundary where Kloosterman saving vanishes ($\max(\alpha_1, \alpha_2) \to 1$, i.e. $k_1 = k_2 = 1$) carried a massive `-6.8639 n` (growing as $-c n (\log n)^2$) parity collapse for Wave 9's kernel $A_\sigma(m) = F_\sigma(m) - K_\sigma(m)$.

Wave 13 introduces the **boundary-damped anti-symmetric kernel**:
$$\widetilde{A}_{n,\sigma}(m) \;:=\; F_\sigma(m) - n^{-\sigma} K_\sigma(m) \;=\; \sum_{d \mid m} \mu(d)\Bigl(d^{-\sigma} - \bigl(n (m / d)\bigr)^{-\sigma}\Bigr).$$

### 1.1 Kernel-Checked Theorems in `DampedBoundaryEuler.lean`

All five main theorems are proved unconditionally in Lean 4 with zero `sorry`, zero warnings, and standard axioms `[propext, Classical.choice, Quot.sound]` only:

1. **`dampedFactor_eq_closed_form`**:
   For every $m \ge 1$,
   $$\widetilde{A}_{n,\sigma}(m) \;=\; \Bigl(1 - (-1)^{\omega(m)}\bigl(n \cdot (m / \operatorname{rad} m)\bigr)^{-\sigma}\Bigr)\, F_\sigma(m).$$
2. **`damped_bilateral_composite_mono`**:
   For every $n \ge 4$, every $x, y \in [2, n]$ with $\omega(x) + \omega(y) \ge 3$, and every $0 < \sigma_1 \le \sigma_2 \le \frac{1}{\log n}$:
   $$\sigma_1^{-2}\,\widetilde{A}_{n,\sigma_1}(x)\widetilde{A}_{n,\sigma_1}(y) \;\le\; \sigma_2^{-2}\,\widetilde{A}_{n,\sigma_2}(x)\widetilde{A}_{n,\sigma_2}(y).$$
   Because $n \cdot (m / \operatorname{rad} m) \ge 4 > 1$ for every $m \ge 1$, even squarefree even-$\omega$ integers carry a strictly positive $(1 - e^{-\sigma \log(n m / \operatorname{rad} m)})$ factor, yielding $\ge 4$ minus-factors and total exponent sum $\log x + \log y + 2\log n \le 4\log n$.
3. **`damped_cofactor_weight_bound`**:
   For every $d \ge 1$, $k \ge 1$, $d k = x \le n$, and $\sigma > 0$:
   $$0 \;\le\; \frac{d^{-\sigma} - (n k)^{-\sigma}}{\sigma} \;\le\; \log\!\left(\frac{n}{x}\right) + 2\log k.$$
   At fixed cofactor $k$, the $\log n$ blowup of Wave 9's $(d^{-\sigma} - k^{-\sigma})/\sigma$ is **completely eliminated**!
4. **`damped_k11_slice_unsigned_bound`**:
   With **zero** Möbius cancellation, the entire $k_1 = k_2 = 1$ ($d_1 + d_2 = n$) binary-Chowla slice satisfies:
   $$\left|\sum_{x=2}^{n-2} \mu(x)\mu(n-x)\frac{x^{-\sigma} - n^{-\sigma}}{\sigma}\frac{(n-x)^{-\sigma} - n^{-\sigma}}{\sigma}\right| \;\le\; \sum_{x=2}^{n-2} \log\!\left(\frac{n}{x}\right)\log\!\left(\frac{n}{n-x}\right) \;\sim\; \left(2 - \frac{\pi^2}{6}\right)n \approx 0.355\,n.$$
   Thus the $k_1 = k_2 = 1$ trivial unsigned bound drops by a full factor of $(\log n)^2$!
5. **`damped_bilateral_goldbach_criterion`**:
   For every $n \ge 4$ and every $0 < \sigma_1 \le \sigma_2 \le \frac{1}{\log n}$:
   $$\Xi_n^{\widetilde{A}}(\sigma_1) - \Xi_n^{\widetilde{A}}(\sigma_2) \;>\; 8\bigl(\lfloor\sqrt{n}\rfloor\lfloor\log_2 n\rfloor\bigr)(\log n)^2 \;\implies\; \exists p, q\text{ prime},\; p + q = n.$$

---

## 2. Numerical Comparison at $n = 50{,}002$

At $n = 50{,}002$ with $\sigma_1 = 0.5 / \log n$, $\sigma_2 = 1.0 / \log n$:
- **Full $\Theta(n)$ signal preserved:** `Tot/n = +0.9081`, `PrPr/n = +1.1814`, `PP/n = 0.00265`, `max_comp = -0.000003 < 0` (every composite strictly negative).
- **`k₁ = k₂ = 1` binary-Chowla slice:** dropped **250×** from `-6.8639 n` (Wave 9) to **`-0.0274 n`** Parity (`-0.0003 n` True).
- **High-$\alpha$ boundary (`max(α₁, α₂) ∈ [0.90, 1.01)`):** flipped from `-1.7631 n` Parity (Wave 9) to **`+0.1889 n`** Parity (`+0.0040 n` True) — 100% of the negative parity mass is evacuated into the optimal-Kloosterman power-saving interior $\max(\alpha_1, \alpha_2) \in [0.70, 0.90]$ (`[0.70,0.80): -0.5493`, `[0.80,0.85): -0.4764`, `[0.85,0.90): -0.1547`).

---

## 3. Kernel Verification Log

- **File:** `/home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/DampedBoundaryEuler.lean`
- **Lean / Mathlib check:** `lake env lean` — **exit 0, zero errors, zero warnings**.
- **Banned-token scan:** `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` — **0 matches**.
- **`#print axioms` audit:** All 5 exported theorems (`dampedFactor_eq_closed_form`, `damped_bilateral_composite_mono`, `damped_cofactor_weight_bound`, `damped_k11_slice_unsigned_bound`, `damped_bilateral_goldbach_criterion`) depend strictly on `[propext, Classical.choice, Quot.sound]`.
