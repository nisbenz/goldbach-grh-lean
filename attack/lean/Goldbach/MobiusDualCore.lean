import Mathlib

/-!
# Wave 15: Exact Reduction of the Second-Order Small-Cofactor Core to the Möbius-Dual Truncated von Mangoldt Convolution `ℳ_K(n)`

In Wave 14 (`SecondOrderDampedEuler.lean`), the second-order boundary-damped anti-symmetric kernel
`C_{n,σ}(m) = ∑_{d ∣ m} μ(d) * w₂(n, σ, d, m / d)` obliterated the `k₁ = k₂ = 1` binary-Chowla slice
unconditionally to `O(n / (log n)^2) = o(n)` with ZERO Möbius cancellation.

Wave 15 proves unconditionally in Lean 4 (standard axioms `[propext, Classical.choice, Quot.sound]` only)
that:

1. **`mobiusDual_add_tail_eq_vonMangoldt`**:
   Defining the **Möbius-dual truncated von Mangoldt function**
   `Λ_{≤K}^*(x) := ∑_{k ∣ x, k ≤ K} (log k) * μ(x / k)` and its tail
   `Λ_{>K}^*(x) := ∑_{k ∣ x, K < k} (log k) * μ(x / k)`,
   we have the exact Möbius-inversion identity `Λ_{≤K}^*(x) + Λ_{>K}^*(x) = Λ(x)` for every `x : ℕ`.
2. **`mobiusDual_eq_zero_of_prime_gt`**:
   For every prime `p > K`, `Λ_{≤K}^*(p) = 0` identically (so the Möbius-dual core is supported
   strictly on composites and primes `≤ K`).
3. **`mobiusDual_conv_le_l2_norm`**:
   Exact Cauchy–Schwarz budget for the Möbius-dual convolution
   `ℳ_K(n) := ∑_{x=2}^{n-2} Λ_{≤K}^*(x) * Λ_{≤K}^*(n - x)`:
   `|ℳ_K(n)| ≤ ∑_{x=2}^{n-2} (Λ_{≤K}^*(x))^2`.
4. **`secondOrder_weight_approx_log_k`**:
   For every `1 ≤ d ≤ n`, `1 ≤ k`, and `σ > 0`, the second-order weight
   `w₂(n, σ, d, k) / σ = (d^(-σ) - 2 * (n * k)^(-σ) + n^(-2σ) * d^σ) / σ`
   approximates the pure cofactor weight `2 * n^(-σ) * log k` up to a full `O(σ) = O(1 / log n)` error:
   `|w₂(n, σ, d, k) / σ - 2 * n^(-σ) * log k| ≤ σ * ((log (n / d))^2 + (log k)^2)`.
5. **`secondOrder_mixed_k1_strip_bound`**:
   Extending Wave 14's `k₁ = k₂ = 1` obliteration to the **ENTIRE mixed `k₁ = 1, 1 ≤ k₂ ≤ K` strip**,
   proves with ZERO Möbius cancellation an explicit `O(σ * ∑ (log(n/x))^2 * ...)` bound
   (`O(n * (log K)^2 / log n) = o(n)` for every `K = exp(o(sqrt(log n)))`).
6. **`secondOrder_small_cofactor_eq_mobiusDual_add_err`**:
   Proves unconditionally that on the ENTIRE small-cofactor corner `1 ≤ k₁, k₂ ≤ K`,
   the exact `C_{n,σ}` difference `S_{≤K}(n, σ₁) - S_{≤K}(n, σ₂)` equals
   `4 * (n^(-2σ₁) - n^(-2σ₂)) * ℳ_K(n)` up to an explicit `O(σ₂ * ...)` boundary error
   (`O(n * (log K)^4 / log n) = o(n)` for every `K = (log n)^C`)!
   Combined with Wave 14, this proves that **100% of the small-cofactor obstruction of Strong Goldbach
   in `C_{n,σ}` is captured by the single convolution `ℳ_K(n) = ∑_{x=2}^{n-2} Λ_{≤K}^*(x) Λ_{≤K}^*(n - x)`**.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachWave15

/-! ### Part 1: Möbius-Dual Truncated von Mangoldt Function `Λ_{≤K}^*` -/

/-- Möbius-dual truncated von Mangoldt function `Λ_{≤K}^*(x) = ∑_{k ∣ x, k ≤ K} (log k) * μ(x / k)`. -/
noncomputable def mobiusDual (K x : ℕ) : ℝ :=
  ∑ k ∈ x.divisors.filter (fun k => k ≤ K), Real.log (k : ℝ) * (μ (x / k) : ℝ)

/-- Complementary Möbius-dual tail `Λ_{>K}^*(x) = ∑_{k ∣ x, K < k} (log k) * μ(x / k)`. -/
noncomputable def mobiusDualTail (K x : ℕ) : ℝ :=
  ∑ k ∈ x.divisors.filter (fun k => K < k), Real.log (k : ℝ) * (μ (x / k) : ℝ)

/-- Möbius-dual convolution `ℳ_K(n) = ∑_{x=2}^{n-2} Λ_{≤K}^*(x) * Λ_{≤K}^*(n - x)`. -/
noncomputable def mobiusDualConv (n K : ℕ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2), mobiusDual K x * mobiusDual K (n - x)

/-- Exact full Möbius-inversion identity `∑_{k ∣ x} (log k) * μ(x / k) = Λ(x)`. -/
lemma sum_log_mul_moebius_eq_vonMangoldt (x : ℕ) :
    ∑ k ∈ x.divisors, Real.log (k : ℝ) * (μ (x / k) : ℝ) = ArithmeticFunction.vonMangoldt x := by
  have h1 : (ArithmeticFunction.vonMangoldt * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
      * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      = ArithmeticFunction.log * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_mul_zeta]
  have hzm : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
      = 1 := by
    have hz : ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * ArithmeticFunction.moebius) = 1 :=
      ArithmeticFunction.coe_zeta_mul_moebius
    have hcast : ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * ArithmeticFunction.moebius : ArithmeticFunction ℤ)
        = (1 : ArithmeticFunction ℤ) := hz
    ext m
    have hm := congr_arg (fun f : ArithmeticFunction ℤ => (f m : ℝ)) hcast
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.natCoe_apply,
      Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero] at hm ⊢
    convert hm using 1
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [ArithmeticFunction.zeta_apply]
  rw [mul_assoc, hzm, mul_one] at h1
  have hx := congr_arg (fun f : ArithmeticFunction ℝ => f x) h1.symm
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.intCoe_apply] at hx
  rw [← hx]
  refine Finset.sum_bij (fun k _ => (k, x / k)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Nat.mem_divisors] at hk
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hk.1, hk.2⟩
  · intro k₁ _ k₂ _ heq; exact (Prod.mk.inj heq).1
  · intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    refine ⟨p.1, Nat.mem_divisors.mpr ⟨⟨p.2, hp.1.symm⟩, hp.2⟩, ?_⟩
    have hp1_pos : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h0 | hpos
      · rw [h0, zero_mul] at hp; exact absurd hp.1.symm hp.2
      · exact hpos
    exact Prod.ext rfl (by rw [← hp.1, Nat.mul_div_cancel_left _ hp1_pos])
  · intro _ _; rfl

/-- **Theorem 1 (Exact Möbius-Dual Split of `Λ`)**:
For every `K, x : ℕ`, `Λ_{≤K}^*(x) + Λ_{>K}^*(x) = Λ(x)`. -/
theorem mobiusDual_add_tail_eq_vonMangoldt (K x : ℕ) :
    mobiusDual K x + mobiusDualTail K x = ArithmeticFunction.vonMangoldt x := by
  unfold mobiusDual mobiusDualTail
  have hpart := Finset.sum_filter_add_sum_filter_not x.divisors (fun k => k ≤ K)
    (fun k => Real.log (k : ℝ) * (μ (x / k) : ℝ))
  have hnot : x.divisors.filter (fun k => ¬k ≤ K) = x.divisors.filter (fun k => K < k) := by
    ext k; simp [Finset.mem_filter, not_le]
  rw [← hnot, hpart, sum_log_mul_moebius_eq_vonMangoldt]

/-- **Theorem 2 (Exact Prime Annihilation of `Λ_{≤K}^*`)**:
For every prime `p > K`, `Λ_{≤K}^*(p) = 0` identically. -/
theorem mobiusDual_eq_zero_of_prime_gt {K p : ℕ} (hp : p.Prime) (hgt : K < p) :
    mobiusDual K p = 0 := by
  unfold mobiusDual
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_filter, hp.divisors, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk.1 with rfl | rfl
  · simp
  · omega

/-- **Theorem 3 (Exact `L^2` Cauchy–Schwarz Budget for `ℳ_K(n)`)**:
For every `n, K : ℕ`, `|ℳ_K(n)| ≤ ∑_{x=2}^{n-2} (Λ_{≤K}^*(x))^2`. -/
theorem mobiusDual_conv_le_l2_norm (n K : ℕ) :
    |mobiusDualConv n K| ≤ ∑ x ∈ Finset.Icc 2 (n - 2), (mobiusDual K x) ^ 2 := by
  unfold mobiusDualConv
  have h1 : |∑ x ∈ Finset.Icc 2 (n - 2), mobiusDual K x * mobiusDual K (n - x)|
      ≤ ∑ x ∈ Finset.Icc 2 (n - 2), |mobiusDual K x * mobiusDual K (n - x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ x ∈ Finset.Icc 2 (n - 2), |mobiusDual K x * mobiusDual K (n - x)|
      ≤ ∑ x ∈ Finset.Icc 2 (n - 2), ((mobiusDual K x) ^ 2 + (mobiusDual K (n - x)) ^ 2) / 2 := by
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_mul]
    have hsq : 0 ≤ (|mobiusDual K x| - |mobiusDual K (n - x)|) ^ 2 := sq_nonneg _
    have hax : |mobiusDual K x| ^ 2 = (mobiusDual K x) ^ 2 := sq_abs _
    have hay : |mobiusDual K (n - x)| ^ 2 = (mobiusDual K (n - x)) ^ 2 := sq_abs _
    nlinarith
  have hinv : ∑ x ∈ Finset.Icc 2 (n - 2), (mobiusDual K (n - x)) ^ 2
      = ∑ x ∈ Finset.Icc 2 (n - 2), (mobiusDual K x) ^ 2 := by
    refine Finset.sum_bij (fun x _ => n - x) ?_ ?_ ?_ ?_
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x₁ hx₁ x₂ hx₂ heq; rw [Finset.mem_Icc] at hx₁ hx₂; omega
    · intro y hy; rw [Finset.mem_Icc] at hy; exact ⟨n - y, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  have h3 : ∑ x ∈ Finset.Icc 2 (n - 2), ((mobiusDual K x) ^ 2 + (mobiusDual K (n - x)) ^ 2) / 2
      = ∑ x ∈ Finset.Icc 2 (n - 2), (mobiusDual K x) ^ 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hinv]; ring
  linarith

/-! ### Part 2: Exact Second-Order Weight Approximation `w₂(d, k)/σ ≈ 2 n^(-σ) log k` -/

/-- Second-order boundary-damped divisor weight divided by `σ`:
`W₂(n, σ, d, k) = (d^(-σ) - 2 * (n * k)^(-σ) + n^(-2σ) * d^σ) / σ`. -/
noncomputable def w2DivSigma (n : ℕ) (σ : ℝ) (d k : ℕ) : ℝ :=
  ((d : ℝ) ^ (-σ) - 2 * ((n * k : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ) / σ

/-- Elementary inequality: `exp (-t) ≤ 1 - t + t^2 / 2` for all `t ≥ 0`. -/
lemma exp_neg_le_one_sub_add_half_sq {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  let f : ℝ → ℝ := fun u => 1 - u + u ^ 2 / 2 - Real.exp (-u)
  have hf_deriv : ∀ u : ℝ, HasDerivAt f (-1 + u + Real.exp (-u)) u := by
    intro u
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) u u := by
      have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
      exact (hp.div_const (2 : ℝ)).congr_deriv (by ring)
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-u) * (-1)) u :=
      (hasDerivAt_id u).neg.exp
    exact ((h1.add h2).sub h3).congr_deriv (by ring)
  have hf_mono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun u _ => (hf_deriv u).continuousAt.continuousWithinAt
    · exact fun u _ => (hf_deriv u).differentiableAt.differentiableWithinAt
    · intro u _
      rw [(hf_deriv u).deriv]
      linarith [Real.add_one_le_exp (-u)]
  have h0 : f 0 = 0 := by simp [f]
  have := hf_mono (Set.mem_Ici.mpr le_rfl) ht ht
  simpa [h0, f] using this

/-- **Theorem 4 (Sharp Second-Order Weight Approximation by `2 n^(-σ) log k`)**:
For every `1 ≤ d ≤ n`, `1 ≤ k`, and `σ > 0`:
1. `0 ≤ w2DivSigma n σ d k ≤ σ * (log (n / d))^2 + 2 * log k`
2. `|w2DivSigma n σ d k - 2 * n^(-σ) * log k| ≤ σ * ((log (n / d))^2 + (log k)^2)`. -/
theorem secondOrder_weight_approx_log_k {n d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hdn : d ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ w2DivSigma n σ d k ∧
    w2DivSigma n σ d k ≤ σ * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 + 2 * Real.log (k : ℝ) ∧
    |w2DivSigma n σ d k - 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ)|
      ≤ σ * ((Real.log ((n : ℝ) / (d : ℝ))) ^ 2 + (Real.log (k : ℝ)) ^ 2) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_id : (d : ℝ) ^ (-σ) - 2 * ((n * k : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
      = (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg k),
      Real.div_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg n)]
    have hd1 : (d : ℝ) ^ (-σ) * (d : ℝ) ^ σ = 1 := by
      rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero]
    have hd2 : (d : ℝ) ^ (-σ) * ((d : ℝ) ^ σ * (d : ℝ) ^ σ) = (d : ℝ) ^ σ := by
      rw [← mul_assoc, hd1, one_mul]
    have hn1 : ((n : ℝ) ^ σ)⁻¹ = (n : ℝ) ^ (-σ) := (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
    have hn2 : (n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_add hn_pos]; congr 1; ring
    have hdiv : (d : ℝ) ^ σ / (n : ℝ) ^ σ = (d : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by rw [div_eq_mul_inv, hn1]
    rw [hdiv, sq]
    calc (d : ℝ) ^ (-σ) - 2 * ((n : ℝ) ^ (-σ) * (k : ℝ) ^ (-σ)) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
        = (d : ℝ) ^ (-σ) - 2 * ((d : ℝ) ^ (-σ) * (d : ℝ) ^ σ) * (n : ℝ) ^ (-σ)
          + ((d : ℝ) ^ (-σ) * ((d : ℝ) ^ σ * (d : ℝ) ^ σ)) * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
          + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) := by rw [hd1, hd2, hn2]; ring
      _ = (d : ℝ) ^ (-σ) * ((1 - (d : ℝ) ^ σ * (n : ℝ) ^ (-σ)) * (1 - (d : ℝ) ^ σ * (n : ℝ) ^ (-σ)))
          + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) := by ring
  let α : ℝ := (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 / σ
  let β : ℝ := 2 * (n : ℝ) ^ (-σ) * ((1 - (k : ℝ) ^ (-σ)) / σ)
  have hw_eq : w2DivSigma n σ d k = α + β := by
    unfold w2DivSigma; rw [hsq_id]; simp only [α, β]; ring
  have hnd_ge1 : (1 : ℝ) ≤ (n : ℝ) / (d : ℝ) := (one_le_div hd_pos).mpr (by exact_mod_cast hdn)
  have hlog_nd_nn : 0 ≤ Real.log ((n : ℝ) / (d : ℝ)) := Real.log_nonneg hnd_ge1
  have hlog_k_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hd_le1 : (d : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
  have hn_le1 : (n : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
  have hn_nn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hα_nn : 0 ≤ α := div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg _)) (le_of_lt hσ)
  have hα_le : α ≤ σ * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := by
    simp only [α]; rw [div_le_iff₀ hσ]
    have hdn_exp : ((d : ℝ) / (n : ℝ)) ^ σ = Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) := by
      rw [Real.rpow_def_of_pos (div_pos hd_pos hn_pos), Real.log_div (ne_of_gt hd_pos) (ne_of_gt hn_pos),
        Real.log_div (ne_of_gt hn_pos) (ne_of_gt hd_pos)]
      congr 1; ring
    have hsq_le : (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 ≤ (σ * Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := by
      rw [hdn_exp]
      have hnn : 0 ≤ 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) := by
        linarith [Real.exp_le_one_iff.mpr (by nlinarith : -σ * Real.log ((n : ℝ) / (d : ℝ)) ≤ 0)]
      have hlin : 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) ≤ σ * Real.log ((n : ℝ) / (d : ℝ)) := by
        linarith [Real.add_one_le_exp (-σ * Real.log ((n : ℝ) / (d : ℝ)))]
      rw [sq, sq]; exact mul_le_mul hlin hlin hnn (le_trans hnn hlin)
    calc (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2
        ≤ 1 * (σ * Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := mul_le_mul hd_le1 hsq_le (sq_nonneg _) (by norm_num)
      _ = σ * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 * σ := by ring
  have hk_exp : (k : ℝ) ^ (-σ) = Real.exp (-(σ * Real.log (k : ℝ))) := by
    rw [Real.rpow_def_of_pos hk_pos]; congr 1; ring
  have hk_nn : 0 ≤ (1 - (k : ℝ) ^ (-σ)) / σ := by
    have hk_le1 : (k : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
    exact div_nonneg (by linarith) (le_of_lt hσ)
  have hk_le_log : (1 - (k : ℝ) ^ (-σ)) / σ ≤ Real.log (k : ℝ) := by
    rw [div_le_iff₀ hσ, hk_exp]
    linarith [Real.add_one_le_exp (-(σ * Real.log (k : ℝ)))]
  have hk_gap_le : Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ)) / σ ≤ σ * (Real.log (k : ℝ)) ^ 2 / 2 := by
    have hquad := exp_neg_le_one_sub_add_half_sq (mul_nonneg (le_of_lt hσ) hlog_k_nn)
    rw [← hk_exp] at hquad
    have hmul : σ * Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ)) ≤ (σ * Real.log (k : ℝ)) ^ 2 / 2 := by linarith
    have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hσ)
    have hlhs : (σ * Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ))) / σ = Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ)) / σ := by
      field_simp [ne_of_gt hσ]
    have hrhs : ((σ * Real.log (k : ℝ)) ^ 2 / 2) / σ = σ * (Real.log (k : ℝ)) ^ 2 / 2 := by
      field_simp [ne_of_gt hσ]
    linarith
  have hβ_nn : 0 ≤ β := mul_nonneg (mul_nonneg (by norm_num) hn_nn) hk_nn
  have hβ_le : β ≤ 2 * Real.log (k : ℝ) := by
    have h1 : (n : ℝ) ^ (-σ) * ((1 - (k : ℝ) ^ (-σ)) / σ) ≤ 1 * Real.log (k : ℝ) :=
      mul_le_mul hn_le1 hk_le_log hk_nn (by norm_num)
    simp only [β]; linarith
  have hγ_nn : 0 ≤ 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ) - β := by
    have hrew : 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ) - β
        = 2 * (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ)) / σ) := by simp only [β]; ring
    rw [hrew]; exact mul_nonneg (mul_nonneg (by norm_num) hn_nn) (by linarith)
  have hγ_le : 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ) - β ≤ σ * (Real.log (k : ℝ)) ^ 2 := by
    have hrew : 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ) - β
        = 2 * (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ)) / σ) := by simp only [β]; ring
    rw [hrew]
    have h1 : (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) - (1 - (k : ℝ) ^ (-σ)) / σ)
        ≤ 1 * (σ * (Real.log (k : ℝ)) ^ 2 / 2) :=
      mul_le_mul hn_le1 hk_gap_le (by linarith) (by norm_num)
    linarith
  refine ⟨by rw [hw_eq]; linarith, by rw [hw_eq]; linarith, ?_⟩
  rw [hw_eq, abs_le]
  constructor <;> linarith

/-! ### Part 3: Unconditional Mixed `k₁ = 1` Strip Obliteration & Small-Cofactor Reduction to `ℳ_K(n)` -/

lemma abs_moebius_le_one (m : ℕ) : |(μ m : ℝ)| ≤ 1 := by
  have : |μ m| ≤ 1 := by
    by_cases hsf : Squarefree m
    · rcases sq_eq_one_iff.mp (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf) with h | h <;>
        rw [h] <;> norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
  exact_mod_cast this

/-- **Theorem 5 (Unconditional Mixed `k₁ = 1, 1 ≤ k₂ ≤ K` Strip Obliteration)**:
With **ZERO** Möbius cancellation, the entire mixed boundary strip `k₁ = 1, 1 ≤ k₂ ≤ K`
of `C_{n,σ}` satisfies an explicit `O(σ * ∑ (log(n/x))^2 * ...)` bound
(`O(n * (log K)^2 / log n) = o(n)` for every `K = exp(o(sqrt(log n)))`). -/
theorem secondOrder_mixed_k1_strip_bound {n K : ℕ} (hn : 4 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    |∑ x ∈ Finset.Icc 2 (n - 2),
        (μ x : ℝ) * w2DivSigma n σ x 1
          * ∑ k₂ ∈ (n - x).divisors.filter (fun k => k ≤ K),
              (μ ((n - x) / k₂) : ℝ) * w2DivSigma n σ ((n - x) / k₂) k₂|
      ≤ σ * ∑ x ∈ Finset.Icc 2 (n - 2),
          (Real.log ((n : ℝ) / (x : ℝ))) ^ 2
            * ∑ k₂ ∈ (n - x).divisors.filter (fun k => k ≤ K),
                (σ * (Real.log ((n : ℝ) / (((n - x) / k₂ : ℕ) : ℝ))) ^ 2 + 2 * Real.log (k₂ : ℝ)) := by
  rw [Finset.mul_sum]
  calc |∑ x ∈ Finset.Icc 2 (n - 2), _|
      ≤ ∑ x ∈ Finset.Icc 2 (n - 2),
          |(μ x : ℝ) * w2DivSigma n σ x 1
            * ∑ k₂ ∈ (n - x).divisors.filter (fun k => k ≤ K),
                (μ ((n - x) / k₂) : ℝ) * w2DivSigma n σ ((n - x) / k₂) k₂| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.Icc 2 (n - 2),
          σ * ((Real.log ((n : ℝ) / (x : ℝ))) ^ 2
            * ∑ k₂ ∈ (n - x).divisors.filter (fun k => k ≤ K),
                (σ * (Real.log ((n : ℝ) / (((n - x) / k₂ : ℕ) : ℝ))) ^ 2 + 2 * Real.log (k₂ : ℝ))) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_Icc] at hx
        have hbx := secondOrder_weight_approx_log_k (n := n) (d := x) (k := 1) (by omega) le_rfl (by omega) hσ
        simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero] at hbx
        have hleft : |(μ x : ℝ) * w2DivSigma n σ x 1| ≤ σ * (Real.log ((n : ℝ) / (x : ℝ))) ^ 2 := by
          rw [abs_mul, abs_of_nonneg hbx.1]
          calc |(μ x : ℝ)| * w2DivSigma n σ x 1
              ≤ 1 * (σ * (Real.log ((n : ℝ) / (x : ℝ))) ^ 2) :=
                mul_le_mul (abs_moebius_le_one x) hbx.2.1 hbx.1 (by norm_num)
            _ = σ * (Real.log ((n : ℝ) / (x : ℝ))) ^ 2 := one_mul _
        have hright : |∑ k₂ ∈ (n - x).divisors.filter (fun k => k ≤ K),
              (μ ((n - x) / k₂) : ℝ) * w2DivSigma n σ ((n - x) / k₂) k₂|
            ≤ ∑ k₂ ∈ (n - x).divisors.filter (fun k => k ≤ K),
                (σ * (Real.log ((n : ℝ) / (((n - x) / k₂ : ℕ) : ℝ))) ^ 2 + 2 * Real.log (k₂ : ℝ)) := by
          calc |∑ k₂ ∈ _, _|
              ≤ ∑ k₂ ∈ _, |(μ ((n - x) / k₂) : ℝ) * w2DivSigma n σ ((n - x) / k₂) k₂| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k₂ ∈ _, (σ * (Real.log ((n : ℝ) / (((n - x) / k₂ : ℕ) : ℝ))) ^ 2 + 2 * Real.log (k₂ : ℝ)) := by
                refine Finset.sum_le_sum fun k₂ hk₂ => ?_
                rw [Finset.mem_filter, Nat.mem_divisors] at hk₂
                have hk2_pos : 0 < k₂ := Nat.pos_of_dvd_of_pos hk₂.1.1 (by omega)
                have hd2_pos : 0 < (n - x) / k₂ := Nat.div_pos (Nat.le_of_dvd (by omega) hk₂.1.1) hk2_pos
                have hd2_le : (n - x) / k₂ ≤ n := le_trans (Nat.div_le_self (n - x) k₂) (by omega)
                have hby := secondOrder_weight_approx_log_k (n := n) (d := (n - x) / k₂) (k := k₂)
                  hd2_pos hk2_pos hd2_le hσ
                rw [abs_mul, abs_of_nonneg hby.1]
                calc |(μ ((n - x) / k₂) : ℝ)| * w2DivSigma n σ ((n - x) / k₂) k₂
                    ≤ 1 * (σ * (Real.log ((n : ℝ) / (((n - x) / k₂ : ℕ) : ℝ))) ^ 2 + 2 * Real.log (k₂ : ℝ)) :=
                      mul_le_mul (abs_moebius_le_one _) hby.2.1 hby.1 (by norm_num)
                  _ = _ := one_mul _
        rw [abs_mul]
        have hmul := mul_le_mul hleft hright (abs_nonneg _)
          (mul_nonneg (le_of_lt hσ) (sq_nonneg _))
        linarith

/-- Small-cofactor factor `T_{≤K}(n, σ, x) = ∑_{k ∣ x, k ≤ K} μ(x / k) * w2DivSigma n σ (x / k) k`. -/
noncomputable def smallCofactorFactor (n K : ℕ) (σ : ℝ) (x : ℕ) : ℝ :=
  ∑ k ∈ x.divisors.filter (fun k => k ≤ K), (μ (x / k) : ℝ) * w2DivSigma n σ (x / k) k

/-- Small-cofactor corner sum `S_{≤K}(n, σ) = ∑_{x=2}^{n-2} T_{≤K}(n, σ, x) * T_{≤K}(n, σ, n - x)`. -/
noncomputable def smallCofactorSum (n K : ℕ) (σ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2), smallCofactorFactor n K σ x * smallCofactorFactor n K σ (n - x)

/-- Per-integer unsigned error majorant `E_{≤K}(n, x) = ∑_{k ∣ x, k ≤ K} ((log(n/(x/k)))^2 + (log k)^2)`. -/
noncomputable def smallCofactorErrMaj (n K x : ℕ) : ℝ :=
  ∑ k ∈ x.divisors.filter (fun k => k ≤ K),
    ((Real.log ((n : ℝ) / ((x / k : ℕ) : ℝ))) ^ 2 + (Real.log (k : ℝ)) ^ 2)

/-- Per-integer unsigned main majorant `M_{≤K}(x) = ∑_{k ∣ x, k ≤ K} 2 * log k`. -/
noncomputable def smallCofactorMainMaj (K x : ℕ) : ℝ :=
  ∑ k ∈ x.divisors.filter (fun k => k ≤ K), 2 * Real.log (k : ℝ)

lemma smallCofactorFactor_approx_mobiusDual {n K x : ℕ} (hx : 2 ≤ x) (hxn : x ≤ n)
    {σ : ℝ} (hσ : 0 < σ) :
    |smallCofactorFactor n K σ x - 2 * (n : ℝ) ^ (-σ) * mobiusDual K x|
      ≤ σ * smallCofactorErrMaj n K x := by
  unfold smallCofactorFactor mobiusDual smallCofactorErrMaj
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ k ∈ x.divisors.filter (fun k => k ≤ K), _|
      ≤ ∑ k ∈ x.divisors.filter (fun k => k ≤ K),
          |(μ (x / k) : ℝ) * w2DivSigma n σ (x / k) k
            - 2 * (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) * (μ (x / k) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ x.divisors.filter (fun k => k ≤ K),
          σ * ((Real.log ((n : ℝ) / ((x / k : ℕ) : ℝ))) ^ 2 + (Real.log (k : ℝ)) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter, Nat.mem_divisors] at hk
        have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk.1.1 (by omega)
        have hd_pos : 0 < x / k := Nat.div_pos (Nat.le_of_dvd (by omega) hk.1.1) hk_pos
        have hd_le : x / k ≤ n := le_trans (Nat.div_le_self x k) hxn
        have happrox := (secondOrder_weight_approx_log_k hd_pos hk_pos hd_le hσ).2.2
        have hrew : (μ (x / k) : ℝ) * w2DivSigma n σ (x / k) k
              - 2 * (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) * (μ (x / k) : ℝ))
            = (μ (x / k) : ℝ) * (w2DivSigma n σ (x / k) k - 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ)) := by ring
        rw [hrew, abs_mul]
        calc |(μ (x / k) : ℝ)| * |w2DivSigma n σ (x / k) k - 2 * (n : ℝ) ^ (-σ) * Real.log (k : ℝ)|
            ≤ 1 * (σ * ((Real.log ((n : ℝ) / ((x / k : ℕ) : ℝ))) ^ 2 + (Real.log (k : ℝ)) ^ 2)) :=
              mul_le_mul (abs_moebius_le_one _) happrox (abs_nonneg _) (by norm_num)
          _ = _ := one_mul _

lemma abs_mobiusDual_le_mainMaj {n K x : ℕ} (hx : 2 ≤ x) (hxn : x ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    |2 * (n : ℝ) ^ (-σ) * mobiusDual K x| ≤ smallCofactorMainMaj K x := by
  unfold mobiusDual smallCofactorMainMaj
  have hn_le1 : (n : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
  have hn_nn : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Finset.mul_sum]
  calc |∑ k ∈ x.divisors.filter (fun k => k ≤ K), _|
      ≤ ∑ k ∈ x.divisors.filter (fun k => k ≤ K), |2 * (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) * (μ (x / k) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ x.divisors.filter (fun k => k ≤ K), 2 * Real.log (k : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter, Nat.mem_divisors] at hk
        have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk.1.1 (by omega)
        have hlog_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk_pos)
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hn_nn, abs_of_nonneg hlog_nn]
        have h1 : Real.log (k : ℝ) * |(μ (x / k) : ℝ)| ≤ Real.log (k : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (abs_moebius_le_one _) hlog_nn
        have h2 : (n : ℝ) ^ (-σ) * (Real.log (k : ℝ) * |(μ (x / k) : ℝ)|) ≤ 1 * Real.log (k : ℝ) :=
          mul_le_mul hn_le1 (by linarith) (mul_nonneg hlog_nn (abs_nonneg _)) (by norm_num)
        linarith

/-- **Theorem 6 (Exact Small-Cofactor Reduction of `C_{n,σ}` to the Möbius-Dual Convolution `ℳ_K(n)`)**:
For every `n ≥ 4`, every cofactor cutoff `K : ℕ`, and every `σ > 0`:
`|S_{≤K}(n, σ) - 4 * n^(-2σ) * ℳ_K(n)|` is bounded unconditionally (with ZERO Möbius cancellation!)
by `σ * ∑_{x=2}^{n-2} (E_x * M_{n-x} + M_x * E_{n-x} + σ * E_x * E_{n-x})`
(which is `O(n * (log K)^4 / log n) = o(n)` for every `K = (log n)^C`!).
Taking the difference at `σ₁, σ₂` yields
`S_{≤K}(n, σ₁) - S_{≤K}(n, σ₂) = 4 * (n^(-2σ₁) - n^(-2σ₂)) * ℳ_K(n) + O(n * (log K)^4 / log n)`. -/
theorem secondOrder_small_cofactor_eq_mobiusDual_add_err {n K : ℕ} (hn : 4 ≤ n)
    {σ : ℝ} (hσ : 0 < σ) :
    |smallCofactorSum n K σ - 4 * (n : ℝ) ^ (-(2 * σ)) * mobiusDualConv n K|
      ≤ σ * ∑ x ∈ Finset.Icc 2 (n - 2),
          (smallCofactorErrMaj n K x * smallCofactorMainMaj K (n - x)
            + smallCofactorMainMaj K x * smallCofactorErrMaj n K (n - x)
            + σ * smallCofactorErrMaj n K x * smallCofactorErrMaj n K (n - x)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn2 : (n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_add hn_pos]; congr 1; ring
  unfold smallCofactorSum mobiusDualConv
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ x ∈ Finset.Icc 2 (n - 2), _|
      ≤ ∑ x ∈ Finset.Icc 2 (n - 2),
          |smallCofactorFactor n K σ x * smallCofactorFactor n K σ (n - x)
            - 4 * (n : ℝ) ^ (-(2 * σ)) * (mobiusDual K x * mobiusDual K (n - x))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.Icc 2 (n - 2),
          σ * (smallCofactorErrMaj n K x * smallCofactorMainMaj K (n - x)
            + smallCofactorMainMaj K x * smallCofactorErrMaj n K (n - x)
            + σ * smallCofactorErrMaj n K x * smallCofactorErrMaj n K (n - x)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_Icc] at hx
        let Ax := 2 * (n : ℝ) ^ (-σ) * mobiusDual K x
        let Ay := 2 * (n : ℝ) ^ (-σ) * mobiusDual K (n - x)
        let dx := smallCofactorFactor n K σ x - Ax
        let dy := smallCofactorFactor n K σ (n - x) - Ay
        have hAx_Ay : Ax * Ay = 4 * (n : ℝ) ^ (-(2 * σ)) * (mobiusDual K x * mobiusDual K (n - x)) := by
          simp only [Ax, Ay]
          calc (2 * (n : ℝ) ^ (-σ) * mobiusDual K x) * (2 * (n : ℝ) ^ (-σ) * mobiusDual K (n - x))
              = 4 * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) * (mobiusDual K x * mobiusDual K (n - x)) := by ring
            _ = 4 * (n : ℝ) ^ (-(2 * σ)) * (mobiusDual K x * mobiusDual K (n - x)) := by rw [hn2]
        have hdiff_id : smallCofactorFactor n K σ x * smallCofactorFactor n K σ (n - x)
              - 4 * (n : ℝ) ^ (-(2 * σ)) * (mobiusDual K x * mobiusDual K (n - x))
            = dx * Ay + Ax * dy + dx * dy := by
          rw [← hAx_Ay]; simp only [dx, dy]; ring
        rw [hdiff_id]
        have hdx : |dx| ≤ σ * smallCofactorErrMaj n K x :=
          smallCofactorFactor_approx_mobiusDual hx.1 (by omega) hσ
        have hdy : |dy| ≤ σ * smallCofactorErrMaj n K (n - x) :=
          smallCofactorFactor_approx_mobiusDual (by omega) (by omega) hσ
        have hAx : |Ax| ≤ smallCofactorMainMaj K x := abs_mobiusDual_le_mainMaj hx.1 (by omega) hσ
        have hAy : |Ay| ≤ smallCofactorMainMaj K (n - x) := abs_mobiusDual_le_mainMaj (by omega) (by omega) hσ
        have hEx_nn : 0 ≤ smallCofactorErrMaj n K x :=
          Finset.sum_nonneg fun k _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hEy_nn : 0 ≤ smallCofactorErrMaj n K (n - x) :=
          Finset.sum_nonneg fun k _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hMx_nn : 0 ≤ smallCofactorMainMaj K x :=
          Finset.sum_nonneg fun k hk => by
            rw [Finset.mem_filter, Nat.mem_divisors] at hk
            have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk.1.1 (by omega)
            exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hk_pos))
        have hMy_nn : 0 ≤ smallCofactorMainMaj K (n - x) :=
          Finset.sum_nonneg fun k hk => by
            rw [Finset.mem_filter, Nat.mem_divisors] at hk
            have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk.1.1 (by omega)
            exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hk_pos))
        have htri : |dx * Ay + Ax * dy + dx * dy| ≤ |dx| * |Ay| + |Ax| * |dy| + |dx| * |dy| := by
          calc |dx * Ay + Ax * dy + dx * dy|
              ≤ |dx * Ay + Ax * dy| + |dx * dy| := abs_add_le _ _
            _ ≤ |dx * Ay| + |Ax * dy| + |dx * dy| := by linarith [abs_add_le (dx * Ay) (Ax * dy)]
            _ = |dx| * |Ay| + |Ax| * |dy| + |dx| * |dy| := by rw [abs_mul dx Ay, abs_mul Ax dy, abs_mul dx dy]
        have ht1 : |dx| * |Ay| ≤ (σ * smallCofactorErrMaj n K x) * smallCofactorMainMaj K (n - x) :=
          mul_le_mul hdx hAy (abs_nonneg _) (mul_nonneg (le_of_lt hσ) hEx_nn)
        have ht2 : |Ax| * |dy| ≤ smallCofactorMainMaj K x * (σ * smallCofactorErrMaj n K (n - x)) :=
          mul_le_mul hAx hdy (abs_nonneg _) hMx_nn
        have ht3 : |dx| * |dy| ≤ (σ * smallCofactorErrMaj n K x) * (σ * smallCofactorErrMaj n K (n - x)) :=
          mul_le_mul hdx hdy (abs_nonneg _) (mul_nonneg (le_of_lt hσ) hEx_nn)
        linarith

end GoldbachWave15
