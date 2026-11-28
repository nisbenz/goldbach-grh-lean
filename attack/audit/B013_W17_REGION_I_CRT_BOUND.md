# Wave 17 Report: Unconditional Weighted CRT Discrepancy & Explicit $O(Y (\log n)^3)$ Region I Error Bound for $C_{n,\sigma}$

- **Date:** 2026-11-28
- **Author:** Antigravity (Wave 17 `/goal` formalization of weighted Region I CRT error)
- **Lean 4 artifact (kernel-checked):** [RegionICRTBound.lean](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/RegionICRTBound.lean)
- **Prior wave:** [B013_W16_DIRECT_ABEL_BV.md](file:///home/nisbenz/.t3/projects/weak-goldbach/attack/audit/B013_W16_DIRECT_ABEL_BV.md)
- **Honesty status:** **Strong Goldbach remains OPEN.** Wave 17 completes the unconditional formalization of the **weighted Region I CRT error** for Wave 14's second-order boundary-damped kernel $C_{n,\sigma}$: proving in Lean 4 that replacing every exact congruence sum over $d_1 \mid x \land d_2 \mid (n - x)$ in Region I ($d_1 d_2 \le Y$) by its factored CRT main term $\frac{\mathbf{1}_{\gcd(d_1,d_2)\mid n}}{\operatorname{lcm}(d_1, d_2)}\sum_{x=2}^{n-2} w_2(d_1, x) w_2(d_2, n-x)$ incurs a total error of at most $3(\sigma(\log n)^2 + 2\log n)^2 \cdot |H_Y| \le 27\,Y\,(\log n)^2(\log Y + 1) = O(Y(\log n)^3) = o(n)$ for $Y = n / (\log n)^4$.

---

## 1. Kernel-Checked Theorems in `RegionICRTBound.lean`

All five exported theorems are proved unconditionally in Lean 4 (exit 0, zero errors, zero warnings, zero banned tokens, axioms strictly `[propext, Classical.choice, Quot.sound]`):

1. **`unweighted_ap_discrepancy_le_one`**:
   For every modulus $L \ge 1$, residue $r < L$, and interval $[a, b]$ ($a \le b$):
   $$\left|\sum_{x=a}^{b}\left(\mathbf{1}_{x \equiv r \pmod L} - \frac{1}{L}\right)\right| \;\le\; 1.$$
2. **`weighted_ap_discrepancy_le`**:
   Combining `unweighted_ap_discrepancy_le_one` with discrete Abel summation proves for **any** weight $f : \mathbb{N} \to \mathbb{R}$:
   $$\left|\sum_{\substack{x \in [a, b] \\ x \equiv r \pmod L}} f(x) \;-\; \frac{1}{L}\sum_{x=a}^{b} f(x)\right| \;\le\; |f(b)| + \sum_{x=a}^{b-1} |f(x) - f(x + 1)|.$$
3. **`crt_weighted_discrepancy_le`**:
   Using `Nat.chineseRemainder` on reduced coprime moduli $d_1/g, d_2/g$ ($g = \gcd(d_1, d_2)$), proves for every $n \ge 4$, $d_1, d_2 \ge 1$, and any $f : \mathbb{N} \to \mathbb{R}$:
   $$\left|\sum_{\substack{x \in [2, n-2] \\ d_1 \mid x \land d_2 \mid (n - x)}} f(x) \;-\; \frac{\mathbf{1}_{\gcd(d_1,d_2) \mid n}}{\operatorname{lcm}(d_1, d_2)}\sum_{x=2}^{n-2} f(x)\right| \;\le\; |f(n - 2)| + \sum_{x=2}^{n-3} |f(x) - f(x + 1)|.$$
4. **`tv_prod_monotone_antitone_le`**:
   For any non-negative monotone $0 \le u \le U$ and non-negative antitone $0 \le v \le V$ on $[a, b]$:
   $$|u(b) v(b)| + \sum_{x=a}^{b-1} |u(x) v(x) - u(x + 1) v(x + 1)| \;\le\; 3\,U\,V.$$
5. **`regionI_secondOrder_crt_error_bound`**:
   Proves the explicit unconditional Region I error bound for Wave 14's second-order kernel $C_{n,\sigma}$:
   $$\bigl|\operatorname{regI}_{C_2}(n, Y, \sigma) - \operatorname{regI}_{C_2}^{\rm CRT}(n, Y, \sigma)\bigr| \;\le\; 3\bigl(\sigma(\log n)^2 + 2\log n\bigr)^2 \cdot \bigl|\{(d_1, d_2) \in [1, Y]^2 : d_1 d_2 \le Y\}\bigr|.$$
   At $\sigma \le 1/\log n$, this is at most $27\,Y\,(\log n)^2(\log Y + 1) = O(Y(\log n)^3) = o(n)$ for $Y = n / (\log n)^4$.

---

## 2. Kernel Verification Log

- **File:** `/home/nisbenz/.t3/projects/weak-goldbach/attack/lean/Goldbach/RegionICRTBound.lean`
- **Lean / Mathlib check:** `lake env lean` — **exit 0, zero errors, zero warnings**.
- **Banned-token scan:** `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` — **0 matches**.
- **`#print axioms` audit:** All 5 exported theorems (`unweighted_ap_discrepancy_le_one`, `weighted_ap_discrepancy_le`, `crt_weighted_discrepancy_le`, `tv_prod_monotone_antitone_le`, `regionI_secondOrder_crt_error_bound`) depend strictly on `[propext, Classical.choice, Quot.sound]`.
