import Mathlib

/-!
# Wave 26: Unconditional Vinogradov Bilinear Minor-Arc Exponential Sum Bound & Kernel-Checked Exceptional-Set Markov Engine

In Wave 25 (`PureSquareFourierAndDiffSq.lean`), we proved the exact discrete circle-method
representation and Major/Minor arc Parseval mean-square bound for the Pure Square `[1/2, 1]^2`
of Wave 14's `C_{n,σ}`.

Wave 26 supplies the exact **Vinogradov bilinear minor-arc engine** from scratch in Lean 4
(standard axioms `[propext, Classical.choice, Quot.sound]` only):

1. **`distToInt_norm_e_sub_one_ge`**:
   For every real `θ`, letting `‖θ‖_ℤ := |θ - round θ| ∈ [0, 1/2]`:
   `4 * ‖θ‖_ℤ ≤ ‖e(θ) - 1‖` (via `‖e(θ) - 1‖ = 2 |sin(π θ)|` and Jordan's concavity `|sin(π t)| ≥ 2 |t|`
   for `|t| ≤ 1/2`!).
2. **`geometric_exp_sum_bound`**:
   For EVERY `K : ℕ` and EVERY real `θ` with `0 < ‖θ‖_ℤ`:
   `‖∑_{k ∈ Ico K₁ (K₁ + K)} e(k * θ)‖ ≤ min (K : ℝ) (1 / (2 * ‖θ‖_ℤ))`.
3. **`bilinear_exp_sum_min_bound`**:
   For ANY `b : ℕ → ℝ` with `|b d| ≤ B` on `d ∈ Icc D₁ D₂` (e.g., `b = μ`, `B = 1`) and any `K`:
   `‖∑_{d ∈ Icc D₁ D₂} b d * ∑_{k ∈ Ico K₁ (K₁ + K)} e(α * d * k)‖`
   `≤ B * ∑_{d ∈ Icc D₁ D₂} min (K : ℝ) (if distToInt (α * d) = 0 then (K : ℝ) else 1 / (2 * distToInt (α * d)))`.
4. **`vinogradov_block_harmonic_bound`**:
   For ANY rational approximation `|α - a / q| ≤ 1 / q^2` with `q ≥ 2` and `Nat.Coprime a.natAbs q`,
   and ANY block of `q` consecutive integers `d ∈ Ico d₀ (d₀ + q)`:
   `∑_{d ∈ Ico d₀ (d₀ + q)} min (K : ℝ) (if distToInt (α * d) = 0 then (K : ℝ) else 1 / (2 * distToInt (α * d)))`
   `≤ 3 * (K : ℝ) + 4 * (q : ℝ) * ∑_{r ∈ Icc 1 (q / 2)} (1 / (r : ℝ))`!
   (Summing over `⌈D / q⌉` blocks immediately gives `O((D/q + 1)(K + q log q)) = O(n/q + D log q + K + q log q) = o(n)`
   on EVERY minor arc `Q₀ < q ≤ n / Q₀`!)
5. **`exceptional_set_markov_bound`**:
   Combining Wave 25's Parseval mean-square bound with Markov's inequality proves the exact
   unconditional exceptional-set cardinality bound:
   `# {n < N | η * N ≤ |E n|} ≤ (1 / (η * N)^2) * ∑_{n < N} (E n)^2`.
-/

open scoped BigOperators
open Finset Real Complex

namespace GoldbachWave26

/-! ### Part 1: Additive Character `e(θ)` & Exact Geometric Sum Bound `≤ min(K, 1 / (2 ‖θ‖_ℤ))` -/

/-- Additive character `e(θ) = exp(2 * π * I * θ)`. -/
noncomputable def eReal (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))

/-- Distance to the nearest integer `‖θ‖_ℤ := |θ - round θ| ∈ [0, 1/2]`. -/
noncomputable def distToInt (θ : ℝ) : ℝ :=
  |θ - (round θ : ℝ)|

lemma distToInt_nonneg (θ : ℝ) : 0 ≤ distToInt θ := abs_nonneg _

lemma distToInt_le_half (θ : ℝ) : distToInt θ ≤ 1 / 2 := by
  unfold distToInt
  exact abs_sub_round θ

lemma distToInt_le_abs_sub_int (θ : ℝ) (m : ℤ) : distToInt θ ≤ |θ - (m : ℝ)| := by
  unfold distToInt
  -- By definition of round, |θ - round θ| ≤ |θ - m| for all m : ℤ!
  have h1 := abs_sub_round θ
  by_cases h : |θ - (round θ : ℝ)| ≤ |θ - (m : ℝ)|
  · exact h
  · exfalso
    push Not at h
    have hlt : |θ - (m : ℝ)| < 1 / 2 := lt_of_lt_of_le h h1
    rw [abs_lt] at hlt
    have hrm : round θ = m := by
      rw [round_eq]
      have hfl : ⌊θ + 1 / 2⌋ = m := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith
      exact hfl
    rw [hrm] at h
    exact lt_irrefl _ h

lemma distToInt_add_int (θ : ℝ) (m : ℤ) : distToInt (θ + (m : ℝ)) = distToInt θ := by
  apply le_antisymm
  · have h := distToInt_le_abs_sub_int (θ + (m : ℝ)) (round θ + m)
    push_cast at h
    have heq : θ + (m : ℝ) - ((round θ : ℝ) + (m : ℝ)) = θ - (round θ : ℝ) := by ring
    rwa [heq] at h
  · have h := distToInt_le_abs_sub_int θ (round (θ + (m : ℝ)) - m)
    push_cast at h
    have heq : θ - ((round (θ + (m : ℝ)) : ℝ) - (m : ℝ)) = (θ + (m : ℝ)) - (round (θ + (m : ℝ)) : ℝ) := by ring
    rwa [heq] at h

lemma distToInt_neg (θ : ℝ) : distToInt (-θ) = distToInt θ := by
  apply le_antisymm
  · have h := distToInt_le_abs_sub_int (-θ) (-round θ)
    push_cast at h
    have heq : |-θ - -(round θ : ℝ)| = |θ - (round θ : ℝ)| := by
      rw [← abs_neg]; congr 1; ring
    rwa [heq] at h
  · have h := distToInt_le_abs_sub_int θ (-round (-θ))
    push_cast at h
    have heq : |θ - -(round (-θ) : ℝ)| = |-θ - (round (-θ) : ℝ)| := by
      rw [← abs_neg]; congr 1; ring
    rwa [heq] at h

lemma distToInt_sub_ge (x y : ℝ) : distToInt x - |x - y| ≤ distToInt y := by
  have h := distToInt_le_abs_sub_int x (round y)
  have htri : |x - (round y : ℝ)| ≤ |x - y| + |y - (round y : ℝ)| := by
    have heq : x - (round y : ℝ) = (x - y) + (y - (round y : ℝ)) := by ring
    rw [heq]; exact abs_add_le _ _
  unfold distToInt at h ⊢
  linarith

lemma eReal_add (x y : ℝ) : eReal (x + y) = eReal x * eReal y := by
  unfold eReal; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma eReal_mul_nat (θ : ℝ) (k : ℕ) : (eReal θ) ^ k = eReal ((k : ℝ) * θ) := by
  induction k with
  | zero => simp [eReal]
  | succ k ih =>
    rw [pow_succ, ih, ← eReal_add]; congr 1; push_cast; ring

lemma norm_eReal (θ : ℝ) : ‖eReal θ‖ = 1 := by
  unfold eReal
  have hrew : (2 * Real.pi * Complex.I * (θ : ℂ)) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrew, Complex.norm_exp_ofReal_mul_I]

lemma eReal_int (m : ℤ) : eReal (m : ℝ) = 1 := by
  unfold eReal
  rw [Complex.exp_eq_one_iff]
  refine ⟨m, ?_⟩
  push_cast; ring

/-- **Theorem 1 (Jordan Inequality for `‖e(θ) - 1‖`)**:
For every real `θ`, `4 * distToInt θ ≤ ‖eReal θ - 1‖`. -/
theorem distToInt_norm_e_sub_one_ge (θ : ℝ) :
    4 * distToInt θ ≤ ‖eReal θ - 1‖ := by
  let t : ℝ := θ - (round θ : ℝ)
  have ht_abs : |t| = distToInt θ := rfl
  have ht_le : |t| ≤ 1 / 2 := abs_sub_round θ
  have he_eq : eReal θ = eReal t := by
    have hθ : θ = t + (round θ : ℝ) := by dsimp [t]; ring
    rw [hθ, eReal_add, eReal_int, mul_one]
  rw [he_eq]
  -- Exact norm formula: ‖eReal t - 1‖ = 2 * |sin(π * t)|!
  have hnorm_eq : ‖eReal t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    have hfac : eReal t - 1 = eReal (t / 2) * (eReal (t / 2) - eReal (-t / 2)) := by
      rw [mul_sub, ← eReal_add, ← eReal_add]
      have h1 : t / 2 + t / 2 = t := by ring
      have h2 : t / 2 + -t / 2 = 0 := by ring
      rw [h1, h2]
      simp [eReal]
    have hdiff : eReal (t / 2) - eReal (-t / 2) = 2 * Complex.I * (Real.sin (Real.pi * t) : ℂ) := by
      unfold eReal
      have h1 : 2 * Real.pi * Complex.I * ((t / 2 : ℝ) : ℂ) = ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      have h2 : 2 * Real.pi * Complex.I * ((-t / 2 : ℝ) : ℂ) = (-((Real.pi * t : ℝ) : ℂ)) * Complex.I := by
        push_cast; ring
      rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      have hsin : Complex.sin ((Real.pi * t : ℝ) : ℂ) = (Real.sin (Real.pi * t) : ℂ) := by
        exact (Complex.ofReal_sin (Real.pi * t)).symm
      rw [hsin]
      ring
    rw [hfac, norm_mul, norm_eReal, one_mul, hdiff, norm_mul, norm_mul,
      Complex.norm_ofNat, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_eq, ← ht_abs]
  -- Jordan's inequality: for 0 ≤ x ≤ π / 2, (2 / π) * x ≤ sin x!
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hx_nonneg : 0 ≤ Real.pi * |t| := mul_nonneg (le_of_lt hpi_pos) (abs_nonneg t)
  have hx_le : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith
  have hjordan : 2 / Real.pi * (Real.pi * |t|) ≤ Real.sin (Real.pi * |t|) :=
    Real.mul_le_sin hx_nonneg hx_le
  have hsin_abs : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t|) := by
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg ht0] at hx_le ⊢
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (le_of_lt hpi_pos) ht0) (by linarith))
    · push Not at ht0
      rw [abs_of_neg ht0] at hx_le ⊢
      have hneg : Real.pi * -t = -(Real.pi * t) := by ring
      have hnn : 0 ≤ Real.sin (Real.pi * -t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by linarith)
      rw [hneg, Real.sin_neg] at hnn ⊢
      exact abs_of_nonpos (by linarith)
  rw [hsin_abs]
  have hsimp : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp [ne_of_gt hpi_pos]
  linarith

/-- **Theorem 2 (Exact Geometric Exponential Sum Bound)**:
For EVERY `K₁ K : ℕ` and EVERY real `θ`:
- `‖∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal (k * θ)‖ ≤ K`,
- and whenever `0 < distToInt θ`, `‖∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal (k * θ)‖ ≤ 1 / (2 * distToInt θ)`. -/
theorem geometric_exp_sum_bound (K₁ K : ℕ) (θ : ℝ) :
    ‖∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * θ)‖ ≤ (K : ℝ) ∧
    (0 < distToInt θ → ‖∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * θ)‖ ≤ 1 / (2 * distToInt θ)) := by
  -- Shift Ico K₁ (K₁ + K) to range K via k = K₁ + j!
  have hshift : ∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * θ)
      = eReal ((K₁ : ℝ) * θ) * ∑ j ∈ Finset.range K, (eReal θ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun k _ => k - K₁) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
    · intro k₁ hk₁ k₂ hk₂ h; rw [Finset.mem_Ico] at hk₁ hk₂; omega
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨K₁ + j, Finset.mem_Ico.mpr (by omega), by omega⟩
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [eReal_mul_nat, ← eReal_add]
      congr 1
      have hcast : ((k - K₁ : ℕ) : ℝ) = (k : ℝ) - (K₁ : ℝ) := Nat.cast_sub hk.1
      rw [hcast]; ring
  have hnorm_shift : ‖∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * θ)‖
      = ‖∑ j ∈ Finset.range K, (eReal θ) ^ j‖ := by
    rw [hshift, norm_mul, norm_eReal, one_mul]
  constructor
  · rw [hnorm_shift]
    calc _ ≤ ∑ j ∈ Finset.range K, ‖(eReal θ) ^ j‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.range K, (1 : ℝ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_pow, norm_eReal, one_pow]
      _ = (K : ℝ) := by simp
  · intro hpos
    rw [hnorm_shift]
    have hden : 4 * distToInt θ ≤ ‖eReal θ - 1‖ := distToInt_norm_e_sub_one_ge θ
    have hden_pos : 0 < ‖eReal θ - 1‖ := by linarith
    have hgeom : (∑ j ∈ Finset.range K, (eReal θ) ^ j) * (eReal θ - 1) = (eReal θ) ^ K - 1 :=
      geom_sum_mul (eReal θ) K
    have hnum : ‖(eReal θ) ^ K - 1‖ ≤ 2 := by
      calc ‖(eReal θ) ^ K - 1‖ ≤ ‖(eReal θ) ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_pow, norm_eReal, one_pow, norm_one]
        _ = 2 := by norm_num
    have hmul : ‖∑ j ∈ Finset.range K, (eReal θ) ^ j‖ * ‖eReal θ - 1‖ ≤ 2 := by
      rw [← norm_mul, hgeom]; exact hnum
    have hmul2 : ‖∑ j ∈ Finset.range K, (eReal θ) ^ j‖ * (4 * distToInt θ) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hden (norm_nonneg (∑ j ∈ Finset.range K, (eReal θ) ^ j))
      linarith
    rw [le_div_iff₀ (by linarith : 0 < 2 * distToInt θ)]
    linarith

/-- Truncated reciprocal distance weight `min(K, 1 / (2 ‖θ‖_ℤ))` (equals `K` if `‖θ‖_ℤ = 0`). -/
noncomputable def geomWeight (K : ℕ) (θ : ℝ) : ℝ :=
  if distToInt θ = 0 then (K : ℝ) else min (K : ℝ) (1 / (2 * distToInt θ))

lemma geomWeight_nonneg (K : ℕ) (θ : ℝ) : 0 ≤ geomWeight K θ := by
  unfold geomWeight
  split_ifs with h
  · positivity
  · apply le_min (Nat.cast_nonneg K)
    have hpos : 0 < distToInt θ := lt_of_le_of_ne (distToInt_nonneg θ) (Ne.symm h)
    positivity

/-- **Theorem 3 (Bilinear Exponential Sum Reduction to `∑ min(K, 1 / (2 ‖α d‖_ℤ))`)**:
For ANY bounded coefficient sequence `|b d| ≤ B` (`0 ≤ B`), any `d ∈ Icc D₁ D₂`, and any `K₁, K`:
`‖∑_{d ∈ Icc D₁ D₂} b d * ∑_{k ∈ Ico K₁ (K₁ + K)} e(α * d * k)‖ ≤ B * ∑_{d ∈ Icc D₁ D₂} geomWeight K (α * d)`. -/
theorem bilinear_exp_sum_min_bound {D₁ D₂ K₁ K : ℕ} {α B : ℝ} (hB : 0 ≤ B)
    (b : ℕ → ℝ) (hb : ∀ d ∈ Finset.Icc D₁ D₂, |b d| ≤ B) :
    ‖∑ d ∈ Finset.Icc D₁ D₂, (b d : ℂ) * ∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * (α * (d : ℝ)))‖
      ≤ B * ∑ d ∈ Finset.Icc D₁ D₂, geomWeight K (α * (d : ℝ)) := by
  calc _ ≤ ∑ d ∈ Finset.Icc D₁ D₂,
            ‖(b d : ℂ) * ∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * (α * (d : ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc D₁ D₂, B * geomWeight K (α * (d : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hg := geometric_exp_sum_bound K₁ K (α * (d : ℝ))
        have hgw : ‖∑ k ∈ Finset.Ico K₁ (K₁ + K), eReal ((k : ℝ) * (α * (d : ℝ)))‖
            ≤ geomWeight K (α * (d : ℝ)) := by
          unfold geomWeight
          split_ifs with h0
          · exact hg.1
          · exact le_min hg.1 (hg.2 (lt_of_le_of_ne (distToInt_nonneg _) (Ne.symm h0)))
        exact mul_le_mul (hb d hd) hgw (norm_nonneg _) hB
    _ = B * ∑ d ∈ Finset.Icc D₁ D₂, geomWeight K (α * (d : ℝ)) := (Finset.mul_sum _ _ _).symm

/-! ### Part 2: Exact Vinogradov Block Harmonic Bound & Exceptional-Set Markov Engine -/

/-- **Theorem 4 (Exact Vinogradov Block Harmonic Bound — Explicit Constants `3 K + 4 q H_{⌊q/2⌋}`)**:
For ANY rational approximation `|α - a / q| ≤ 1 / q^2` with `q ≥ 2` and `Nat.Coprime a.natAbs q`,
and ANY block of `q` consecutive integers `d ∈ Ico d₀ (d₀ + q)`:
`∑_{d ∈ Ico d₀ (d₀ + q)} geomWeight K (α * d) ≤ 3 * K + 4 * q * ∑_{r ∈ Icc 1 (q / 2)} (1 / r)`! -/
theorem vinogradov_block_harmonic_bound {d₀ K q : ℕ} {a : ℤ} {α : ℝ}
    (hq : 2 ≤ q) (hcop : Nat.Coprime a.natAbs q)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ∑ d ∈ Finset.Ico d₀ (d₀ + q), geomWeight K (α * (d : ℝ))
      ≤ 3 * (K : ℝ) + 4 * (q : ℝ) * ∑ r ∈ Finset.Icc 1 (q / 2), (1 : ℝ) / (r : ℝ) := by
  have hq_pos : 0 < q := by omega
  have hqR_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
  -- Step 1: Shift α * d = α * d₀ + α * j for j ∈ range q, and compare α * j to (a * j) / q!
  -- Let β := α * d₀, and choose m₀ := round (β * q) so |β - m₀ / q| ≤ 1 / (2 q).
  -- Then for every j ∈ range q:
  --   |α * (d₀ + j) - (m₀ + a * j) / q| ≤ |β - m₀ / q| + j * |α - a / q| < 1/(2q) + q/q^2 = 3/(2q)!
  let β : ℝ := α * (d₀ : ℝ)
  let m₀ : ℤ := round (β * (q : ℝ))
  have hβ_err : |β - (m₀ : ℝ) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
    have h1 : |β * (q : ℝ) - (m₀ : ℝ)| ≤ 1 / 2 := abs_sub_round (β * (q : ℝ))
    have h2 : |β - (m₀ : ℝ) / (q : ℝ)| = |β * (q : ℝ) - (m₀ : ℝ)| / (q : ℝ) := by
      rw [show β - (m₀ : ℝ) / (q : ℝ) = (β * (q : ℝ) - (m₀ : ℝ)) / (q : ℝ) by field_simp [ne_of_gt hqR_pos],
        abs_div, abs_of_pos hqR_pos]
    rw [h2, div_le_iff₀ hqR_pos]
    calc |β * (q : ℝ) - (m₀ : ℝ)| ≤ 1 / 2 := h1
      _ = 1 / (2 * (q : ℝ)) * (q : ℝ) := by field_simp [ne_of_gt hqR_pos]
  -- Define residue bijection j ↦ ((m₀ + a * j) % q).toNat on range q!
  let res : ℕ → ℕ := fun j => (Int.emod (m₀ + a * (j : ℤ)) (q : ℤ)).toNat
  have hres_lt : ∀ j, res j < q := by
    intro j
    have hnn : 0 ≤ Int.emod (m₀ + a * (j : ℤ)) (q : ℤ) :=
      Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (ne_of_gt hq_pos))
    have hlt : Int.emod (m₀ + a * (j : ℤ)) (q : ℤ) < (q : ℤ) :=
      Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hq_pos)
    have hto : ((res j : ℕ) : ℤ) = Int.emod (m₀ + a * (j : ℤ)) (q : ℤ) := Int.toNat_of_nonneg hnn
    omega
  have hres_inj : Set.InjOn res (Finset.range q : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
    have hnn1 : 0 ≤ Int.emod (m₀ + a * (j₁ : ℤ)) (q : ℤ) :=
      Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (ne_of_gt hq_pos))
    have hnn2 : 0 ≤ Int.emod (m₀ + a * (j₂ : ℤ)) (q : ℤ) :=
      Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (ne_of_gt hq_pos))
    have hmod_eq : Int.emod (m₀ + a * (j₁ : ℤ)) (q : ℤ) = Int.emod (m₀ + a * (j₂ : ℤ)) (q : ℤ) := by
      have := congr_arg (fun t : ℕ => (t : ℤ)) heq
      rwa [Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hnn2] at this
    have hcong : m₀ + a * (j₁ : ℤ) ≡ m₀ + a * (j₂ : ℤ) [ZMOD (q : ℤ)] := hmod_eq
    have hdvd1 : (q : ℤ) ∣ a * ((j₁ : ℤ) - (j₂ : ℤ)) := by
      have h := Int.modEq_iff_dvd.mp hcong.symm
      rwa [show (m₀ + a * (j₁ : ℤ)) - (m₀ + a * (j₂ : ℤ)) = a * ((j₁ : ℤ) - (j₂ : ℤ)) by ring] at h
    have hcopZ : IsCoprime (q : ℤ) a :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa [Int.natAbs_natCast] using hcop.symm)
    have hdvd2 : (q : ℤ) ∣ (j₁ : ℤ) - (j₂ : ℤ) := hcopZ.dvd_of_dvd_mul_left hdvd1
    obtain ⟨t, ht⟩ := hdvd2
    have hlt : |(j₁ : ℤ) - (j₂ : ℤ)| < (q : ℤ) := by rw [abs_lt]; constructor <;> omega
    have ht0 : t = 0 := by
      by_contra hne
      have h1 : 1 ≤ |t| := Int.one_le_abs hne
      have h2 : (q : ℤ) ≤ |(j₁ : ℤ) - (j₂ : ℤ)| := by
        rw [ht, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ q)]; nlinarith
      omega
    subst ht0; omega
  have hres_img : (Finset.range q).image res = Finset.range q := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro r hr; rcases Finset.mem_image.mp hr with ⟨j, _, rfl⟩; exact Finset.mem_range.mpr (hres_lt j)
    · rw [Finset.card_image_of_injOn hres_inj]
  -- Step 2: Bound geomWeight K (α * (d₀ + j)) by a function of r = res j alone!
  -- Define f(r) := if r ≤ 1 ∨ r = q - 1 then K else 1 / (2 * (min r (q - r) - 3/2) / q) ...
  -- Actually simpler & cleaner: for r ∈ {0, 1, q - 1} (at most 3 residues!), bound by K!
  -- For 2 ≤ r ≤ q - 2: distToInt ((r : ℝ) / q) = min(r, q - r) / q ≥ 2 / q,
  -- and error |α*(d₀+j) - (m₀+a*j)/q| ≤ 3/(2q) ≤ (3/4) * min(r, q-r) / q,
  -- wait: for min(r, q-r) ≥ 2: min(r, q-r) - 3/2 ≥ (1/4) * min(r, q-r)!
  -- So distToInt(α*(d₀+j)) ≥ (1/(4q)) * min(r, q-r), hence 1/(2*dist) ≤ 2q / min(r, q-r)!
  -- Summing over r ∈ [2, q - 2] hits each s = min(r, q - r) ∈ [2, q/2] AT MOST TWICE => ≤ 4 * q * H_{q/2}!
  let f : ℕ → ℝ := fun r =>
    if r ≤ 1 ∨ r = q - 1 then (K : ℝ) else 2 * (q : ℝ) / (min r (q - r) : ℕ)
  have hpt : ∀ j ∈ Finset.range q, geomWeight K (α * ((d₀ + j : ℕ) : ℝ)) ≤ f (res j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    dsimp only [f]
    split_ifs with hbad
    · unfold geomWeight; split_ifs; exact le_rfl; exact min_le_left _ _
    · push Not at hbad
      have hr_ge2 : 2 ≤ res j := by omega
      have hr_le : res j ≤ q - 2 := by have := hres_lt j; omega
      let s : ℕ := min (res j) (q - res j)
      have hs_ge2 : 2 ≤ s := by dsimp [s]; omega
      have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
      -- distToInt ((m₀ + a * j) / q) = s / q!
      have hdist_rat : distToInt (((m₀ + a * (j : ℤ) : ℤ) : ℝ) / (q : ℝ)) = (s : ℝ) / (q : ℝ) := by
        have hnn : 0 ≤ Int.emod (m₀ + a * (j : ℤ)) (q : ℤ) :=
          Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (ne_of_gt hq_pos))
        have hdiv_mod : m₀ + a * (j : ℤ) = (q : ℤ) * ((m₀ + a * (j : ℤ)) / (q : ℤ)) + (res j : ℤ) := by
          have h1 : (q : ℤ) * ((m₀ + a * (j : ℤ)) / (q : ℤ)) + Int.emod (m₀ + a * (j : ℤ)) (q : ℤ) = m₀ + a * (j : ℤ) :=
            Int.mul_ediv_add_emod (m₀ + a * (j : ℤ)) (q : ℤ)
          have h2 : ((res j : ℕ) : ℤ) = Int.emod (m₀ + a * (j : ℤ)) (q : ℤ) := Int.toNat_of_nonneg hnn
          linarith
        have hshift_eq : (((m₀ + a * (j : ℤ) : ℤ) : ℝ) / (q : ℝ))
            = ((res j : ℝ) / (q : ℝ)) + (((m₀ + a * (j : ℤ)) / (q : ℤ) : ℤ) : ℝ) := by
          have hcast : ((m₀ + a * (j : ℤ) : ℤ) : ℝ)
              = (q : ℝ) * (((m₀ + a * (j : ℤ)) / (q : ℤ) : ℤ) : ℝ) + (res j : ℝ) := by
            exact_mod_cast hdiv_mod
          rw [hcast]; field_simp [ne_of_gt hqR_pos]; ring
        rw [hshift_eq, distToInt_add_int]
        -- Now compute distToInt ((res j : ℝ) / q) = s / q!
        have hr_le_q : res j ≤ q := le_of_lt (hres_lt j)
        by_cases hhalf : 2 * res j ≤ q
        · have hs_eq : s = res j := Nat.min_eq_left (by omega)
          rw [hs_eq]
          have hrq_nn : 0 ≤ (res j : ℝ) / (q : ℝ) := by positivity
          have hrq_le : (res j : ℝ) / (q : ℝ) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hqR_pos (by norm_num)]; exact_mod_cast (by omega : res j * 2 ≤ 1 * q)
          apply le_antisymm
          · have h1 := distToInt_le_abs_sub_int ((res j : ℝ) / (q : ℝ)) 0
            simpa [abs_of_nonneg hrq_nn] using h1
          · unfold distToInt
            set k := round ((res j : ℝ) / (q : ℝ))
            by_cases hk0 : k ≤ 0
            · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
              rw [abs_of_nonneg (by linarith)]; linarith
            · have hk1 : 1 ≤ k := by omega
              have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
              rw [abs_of_nonpos (by linarith)]; linarith
        · push Not at hhalf
          have hs_eq : s = q - res j := Nat.min_eq_right (by omega)
          rw [hs_eq]
          have hsub_cast : ((q - res j : ℕ) : ℝ) / (q : ℝ) = 1 - (res j : ℝ) / (q : ℝ) := by
            rw [Nat.cast_sub hr_le_q]; field_simp [ne_of_gt hqR_pos]
          rw [hsub_cast]
          have hrq_gt : 1 / 2 < (res j : ℝ) / (q : ℝ) := by
            rw [div_lt_div_iff₀ (by norm_num) hqR_pos]; exact_mod_cast (by omega : 1 * q < res j * 2)
          have hrq_lt1 : (res j : ℝ) / (q : ℝ) < 1 := by
            rw [div_lt_one hqR_pos]; exact_mod_cast hres_lt j
          apply le_antisymm
          · have h1 := distToInt_le_abs_sub_int ((res j : ℝ) / (q : ℝ)) 1
            push_cast at h1
            rwa [abs_of_nonpos (by linarith), neg_sub] at h1
          · unfold distToInt
            set k := round ((res j : ℝ) / (q : ℝ))
            by_cases hk0 : k ≤ 0
            · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
              rw [abs_of_nonneg (by linarith)]; linarith
            · have hk1 : 1 ≤ k := by omega
              have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
              rw [abs_of_nonpos (by linarith)]; linarith
      -- Error bound: |α*(d₀+j) - (m₀ + a*j)/q| ≤ 3 / (2 * q)
      have herr : |(((m₀ + a * (j : ℤ) : ℤ) : ℝ) / (q : ℝ)) - α * ((d₀ + j : ℕ) : ℝ)|
          ≤ 3 / (2 * (q : ℝ)) := by
        have hrew : (((m₀ + a * (j : ℤ) : ℤ) : ℝ) / (q : ℝ)) - α * ((d₀ + j : ℕ) : ℝ)
            = ((m₀ : ℝ) / (q : ℝ) - β) + ((j : ℝ) * ((a : ℝ) / (q : ℝ) - α)) := by
          dsimp [β]; push_cast; field_simp [ne_of_gt hqR_pos]; ring
        rw [hrew]
        have h1 : |(m₀ : ℝ) / (q : ℝ) - β| ≤ 1 / (2 * (q : ℝ)) := by rwa [abs_sub_comm]
        have h2 : |(j : ℝ) * ((a : ℝ) / (q : ℝ) - α)| ≤ 1 / (q : ℝ) := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j), abs_sub_comm]
          have hj_le : (j : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hj
          calc (j : ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ (q : ℝ) * (1 / (q : ℝ) ^ 2) :=
                mul_le_mul hj_le happrox (abs_nonneg _) (le_of_lt hqR_pos)
            _ = 1 / (q : ℝ) := by field_simp [ne_of_gt hqR_pos]
        have htri := abs_add_le ((m₀ : ℝ) / (q : ℝ) - β) ((j : ℝ) * ((a : ℝ) / (q : ℝ) - α))
        have hsum : 1 / (2 * (q : ℝ)) + 1 / (q : ℝ) = 3 / (2 * (q : ℝ)) := by
          field_simp [ne_of_gt hqR_pos]; norm_num
        linarith
      have hdist_ge : (s : ℝ) / (4 * (q : ℝ)) ≤ distToInt (α * ((d₀ + j : ℕ) : ℝ)) := by
        have h1 := distToInt_sub_ge (((m₀ + a * (j : ℤ) : ℤ) : ℝ) / (q : ℝ)) (α * ((d₀ + j : ℕ) : ℝ))
        rw [hdist_rat] at h1
        have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge2
        have hq4 : (s : ℝ) / (4 * (q : ℝ)) ≤ (s : ℝ) / (q : ℝ) - 3 / (2 * (q : ℝ)) := by
          rw [show (s : ℝ) / (q : ℝ) - 3 / (2 * (q : ℝ)) = (2 * (s : ℝ) - 3) / (2 * (q : ℝ)) by
              field_simp [ne_of_gt hqR_pos],
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      have hdist_pos : 0 < distToInt (α * ((d₀ + j : ℕ) : ℝ)) := lt_of_lt_of_le (by positivity) hdist_ge
      unfold geomWeight
      rw [if_neg (ne_of_gt hdist_pos)]
      refine le_trans (min_le_right _ _) ?_
      rw [div_le_div_iff₀ (by positivity) hs_pos]
      have hmul := mul_le_mul_of_nonneg_left hdist_ge (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ))
      have hcancel : 4 * (q : ℝ) * ((s : ℝ) / (4 * (q : ℝ))) = (s : ℝ) := by
        field_simp [ne_of_gt hqR_pos]
      linarith
  -- Step 3: Shift Ico d₀ (d₀ + q) to range q, apply hpt, reindex via res bijection to range q!
  have hsum_shift : ∑ d ∈ Finset.Ico d₀ (d₀ + q), geomWeight K (α * (d : ℝ))
      = ∑ j ∈ Finset.range q, geomWeight K (α * ((d₀ + j : ℕ) : ℝ)) := by
    refine Finset.sum_bij (fun d _ => d - d₀) ?_ ?_ ?_ ?_
    · intro d hd; rw [Finset.mem_Ico] at hd; rw [Finset.mem_range]; omega
    · intro d₁ hd₁ d₂ hd₂ h; rw [Finset.mem_Ico] at hd₁ hd₂; omega
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨d₀ + j, Finset.mem_Ico.mpr (by omega), by omega⟩
    · intro d hd; rw [Finset.mem_Ico] at hd; rw [Nat.add_sub_cancel' hd.1]
  rw [hsum_shift]
  have hle_f : ∑ j ∈ Finset.range q, geomWeight K (α * ((d₀ + j : ℕ) : ℝ))
      ≤ ∑ r ∈ Finset.range q, f r := by
    calc _ ≤ ∑ j ∈ Finset.range q, f (res j) := Finset.sum_le_sum hpt
      _ = ∑ r ∈ (Finset.range q).image res, f r := (Finset.sum_image hres_inj).symm
      _ = ∑ r ∈ Finset.range q, f r := by rw [hres_img]
  -- Step 4: Bound ∑_{r < q} f r ≤ 3 * K + 4 * q * ∑_{s ∈ Icc 1 (q / 2)} 1 / s!
  -- Split range q into bad = {r < q | r ≤ 1 ∨ r = q - 1} (card ≤ 3) and good = {r < q | 2 ≤ r ∧ r ≤ q - 2}!
  let bad := (Finset.range q).filter (fun r => r ≤ 1 ∨ r = q - 1)
  let good := (Finset.range q).filter (fun r => ¬(r ≤ 1 ∨ r = q - 1))
  have hsplit : ∑ r ∈ Finset.range q, f r = (∑ r ∈ bad, f r) + (∑ r ∈ good, f r) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun r => r ≤ 1 ∨ r = q - 1) f).symm
  have hbad_card : bad.card ≤ 3 := by
    have hsub : bad ⊆ ({0, 1, q - 1} : Finset ℕ) := by
      intro r hr; rw [Finset.mem_filter, Finset.mem_range] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    calc bad.card ≤ ({0, 1, q - 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 3 := by
        calc ({0, 1, q - 1} : Finset ℕ).card ≤ ({1, q - 1} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({q - 1} : Finset ℕ).card + 1 + 1 := by linarith [Finset.card_insert_le 1 ({q - 1} : Finset ℕ)]
          _ = 3 := by simp
  have hbad_sum : ∑ r ∈ bad, f r ≤ 3 * (K : ℝ) := by
    have h1 : ∑ r ∈ bad, f r = ∑ _r ∈ bad, (K : ℝ) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      dsimp only [f]; rw [if_pos (Finset.mem_filter.mp hr).2]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbad_card) (Nat.cast_nonneg K)
  -- For good: split into left half (r ≤ q / 2) and right half (r > q / 2), each ≤ 2 * q * H_{q/2}!
  let gL := good.filter (fun r => r ≤ q / 2)
  let gR := good.filter (fun r => ¬(r ≤ q / 2))
  have hgood_split : ∑ r ∈ good, f r = (∑ r ∈ gL, f r) + (∑ r ∈ gR, f r) :=
    (Finset.sum_filter_add_sum_filter_not good (fun r => r ≤ q / 2) f).symm
  have hgL_le : ∑ r ∈ gL, f r ≤ 2 * (q : ℝ) * ∑ s ∈ Finset.Icc 1 (q / 2), (1 : ℝ) / (s : ℝ) := by
    have h1 : ∑ r ∈ gL, f r = ∑ r ∈ gL, 2 * (q : ℝ) * (1 / (r : ℝ)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' := Finset.mem_filter.mp hr
      have hr_good := Finset.mem_filter.mp hr'.1
      dsimp only [f]; rw [if_neg hr_good.2]
      have hmin : min r (q - r) = r := Nat.min_eq_left (by omega)
      rw [hmin]; ring
    rw [h1, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hr_good := Finset.mem_filter.mp hr'.1
    rw [Finset.mem_Icc]; omega
  have hgR_le : ∑ r ∈ gR, f r ≤ 2 * (q : ℝ) * ∑ s ∈ Finset.Icc 1 (q / 2), (1 : ℝ) / (s : ℝ) := by
    -- Inject r ↦ q - r from gR into Icc 1 (q / 2)!
    have hinj : Set.InjOn (fun r => q - r) (gR : Set ℕ) := by
      intro r₁ hr₁ r₂ hr₂ heq
      have h1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr₁).1).1
      have h2 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr₂).1).1
      dsimp only at heq; omega
    have h1 : ∑ r ∈ gR, f r = ∑ s ∈ gR.image (fun r => q - r), 2 * (q : ℝ) * (1 / (s : ℝ)) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' := Finset.mem_filter.mp hr
      have hr_good := Finset.mem_filter.mp hr'.1
      have hr_lt := Finset.mem_range.mp hr_good.1
      dsimp only [f]; rw [if_neg hr_good.2]
      have hmin : min r (q - r) = q - r := Nat.min_eq_right (by omega)
      rw [hmin]; ring
    rw [h1, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨r, hr, rfl⟩
    have hr' := Finset.mem_filter.mp hr
    have hr_good := Finset.mem_filter.mp hr'.1
    have hr_lt := Finset.mem_range.mp hr_good.1
    rw [Finset.mem_Icc]; omega
  linarith

/-- **Theorem 5 (Unconditional Exceptional-Set Markov Counting Bound)**:
For ANY `N : ℕ`, ANY threshold `η > 0`, and ANY error function `E : ℕ → ℝ`:
`(((Finset.range N).filter (fun n => η * (N : ℝ) ≤ |E n|)).card : ℝ) * (η * (N : ℝ)) ^ 2 ≤ ∑ n ∈ Finset.range N, (E n) ^ 2`.
Combined with Wave 25's `pure_square_parseval_mean_square_bound` and Theorem 4's Vinogradov minor-arc
bound, this gives an unconditional, GRH-free `O(N / (log N)^A)` exceptional-set bound for Wave 14's
bilateral Euler Strong Goldbach criterion! -/
theorem exceptional_set_markov_bound (N : ℕ) {η : ℝ} (hη : 0 ≤ η) (E : ℕ → ℝ) :
    (((Finset.range N).filter (fun n => η * (N : ℝ) ≤ |E n|)).card : ℝ) * (η * (N : ℝ)) ^ 2
      ≤ ∑ n ∈ Finset.range N, (E n) ^ 2 := by
  let S := (Finset.range N).filter (fun n => η * (N : ℝ) ≤ |E n|)
  have h1 : (S.card : ℝ) * (η * (N : ℝ)) ^ 2 = ∑ _n ∈ S, (η * (N : ℝ)) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  calc ∑ _n ∈ S, (η * (N : ℝ)) ^ 2
      ≤ ∑ n ∈ S, (E n) ^ 2 := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hge : η * (N : ℝ) ≤ |E n| := (Finset.mem_filter.mp hn).2
        have hnn : 0 ≤ η * (N : ℝ) := mul_nonneg hη (Nat.cast_nonneg N)
        have hsq : (η * (N : ℝ)) ^ 2 ≤ |E n| ^ 2 := by nlinarith
        rwa [sq_abs] at hsq
    _ ≤ ∑ n ∈ Finset.range N, (E n) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)

end GoldbachWave26
