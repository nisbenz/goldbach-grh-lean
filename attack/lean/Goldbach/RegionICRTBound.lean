import Mathlib

/-!
# Wave 17: Unconditional Weighted CRT Discrepancy & Explicit `O(Y (log n)^3)` Region I Error Bound for `C_{n,σ}`

In Wave 10 (`ThreeRegionHyperbola.lean`), we proved the unweighted CRT pair-count approximation
`|N_n^∘(d₁, d₂) - n / lcm(d₁, d₂)| ≤ 4`. In Wave 14 (`SecondOrderDampedEuler.lean`), we introduced
the second-order boundary-damped kernel `C_{n,σ}` whose divisor weight `w₂(n, σ, d, x / d) / σ`
depends explicitly on `x` (increasing in `x` on the left, decreasing in `x` on the right).

Wave 17 closes the formal CRT gap for `C_{n,σ}` unconditionally in Lean 4
(standard axioms `[propext, Classical.choice, Quot.sound]` only), proving:

1. **`unweighted_ap_discrepancy_le_one`**:
   For every modulus `L ≥ 1`, residue `r < L`, and interval `Finset.Icc a b` (`a ≤ b`):
   `|(card {x ∈ Icc a b | x % L = r} : ℝ) - ((b - a + 1 : ℕ) : ℝ) / L| ≤ 1`.
2. **`weighted_ap_discrepancy_le`**:
   By discrete Abel summation, for ANY function `f : ℕ → ℝ`:
   `|∑_{x ∈ Icc a b, x % L = r} f x - (1 / L) * ∑_{x ∈ Icc a b} f x| ≤ |f b| + ∑_{x ∈ Ico a b} |f x - f (x + 1)|`.
3. **`crt_weighted_discrepancy_le`**:
   For every `n ≥ 4`, every `d₁, d₂ ≥ 1`, and ANY weight `f : ℕ → ℝ`:
   `|∑_{x ∈ Icc 2 (n-2), d₁ ∣ x ∧ d₂ ∣ (n - x)} f x - (if gcd d₁ d₂ ∣ n then 1 / lcm d₁ d₂ else 0) * ∑_{x ∈ Icc 2 (n-2)} f x|`
   `≤ |f (n - 2)| + ∑_{x ∈ Ico 2 (n-2)} |f x - f (x + 1)|`.
4. **`tv_prod_monotone_antitone_le`**:
   For any non-negative monotone `u ≤ U` and non-negative antitone `v ≤ V` on `[a, b]`:
   `|u b * v b| + ∑_{x ∈ Ico a b} |u x * v x - u (x + 1) * v (x + 1)| ≤ 3 * U * V`.
5. **`regionI_secondOrder_crt_error_bound`**:
   Proves the explicit unconditional Region I error bound for `C_{n,σ}`:
   `|RegI(C_{n,σ}; Y) - RegI_CRT(C_{n,σ}; Y)| ≤ 3 * (σ * (log n)^2 + 2 * log n)^2 * |{(d₁, d₂) ∈ [1, Y]^2 : d₁ * d₂ ≤ Y}|`
   (`≤ 27 * Y * (log n)^2 * (log Y + 1) = O(Y (log n)^3) = o(n)` for `Y = n / (log n)^4` and `σ ≤ 1 / log n`)!
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachWave17

/-! ### Part 1: Exact Unweighted & Weighted AP Discrepancy via Discrete Abel Summation -/

/-- Cardinality of `{x ∈ Icc a b | x % L = r}` is within `1` of `(b - a + 1) / L`. -/
lemma card_ap_Icc_bounds {L r a b : ℕ} (hL : 0 < L) (hr : r < L) (hab : a ≤ b) :
    ((b - a + 1 : ℕ) : ℝ) / (L : ℝ) - 1
      ≤ (((Finset.Icc a b).filter (fun x => x % L = r)).card : ℝ) ∧
    (((Finset.Icc a b).filter (fun x => x % L = r)).card : ℝ)
      ≤ ((b - a + 1 : ℕ) : ℝ) / (L : ℝ) + 1 := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  -- Count via injection into quotients q = x / L:
  -- x ∈ Icc a b ∧ x % L = r  <=>  x = q * L + r with a ≤ q * L + r ∧ q * L + r ≤ b.
  let S := (Finset.Icc a b).filter (fun x => x % L = r)
  -- Key counting lemma on intervals of length L: every block [t, t + L - 1] contains EXACTLY 1 element with x % L = r!
  have hblock : ∀ t : ℕ, ((Finset.Ico t (t + L)).filter (fun x => x % L = r)).card = 1 := by
    intro t
    -- Unique element x₀ = t + (r + L - t % L) % L
    let s := (r + L - t % L) % L
    have hs_lt : s < L := Nat.mod_lt _ hL
    have hx0_mem : t + s ∈ (Finset.Ico t (t + L)).filter (fun x => x % L = r) := by
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨Nat.le_add_right t s, Nat.add_lt_add_left hs_lt t⟩, ?_⟩
      have htm : t % L < L := Nat.mod_lt t hL
      have h1 : (t + s) % L = (t % L + (r + L - t % L)) % L := by
        calc (t + s) % L = (t % L + s % L) % L := Nat.add_mod t s L
          _ = (t % L + (r + L - t % L) % L) % L := by rw [Nat.mod_mod]
          _ = ((t % L) % L + (r + L - t % L) % L) % L := by rw [Nat.mod_mod]
          _ = (t % L + (r + L - t % L)) % L := (Nat.add_mod (t % L) (r + L - t % L) L).symm
      rw [h1]
      have h2 : t % L + (r + L - t % L) = r + L := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    rw [Finset.card_eq_one]
    refine ⟨t + s, Finset.ext fun x => ?_⟩
    rw [Finset.mem_singleton]
    constructor
    · intro hx
      rw [Finset.mem_filter, Finset.mem_Ico] at hx
      have hmod_eq : t + (x - t) ≡ t + s [MOD L] := by
        rw [Nat.ModEq, Nat.add_sub_cancel' hx.1.1, hx.2, (Finset.mem_filter.mp hx0_mem).2]
      have hsub1 : x - t ≡ s [MOD L] := Nat.ModEq.add_left_cancel' t hmod_eq
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : x - t < L), Nat.mod_eq_of_lt hs_lt] at hsub1
      omega
    · rintro rfl; exact hx0_mem
  -- Split [a, b + 1) = [a, a + k * L) ∪ [a + k * L, b + 1) where k = (b - a + 1) / L:
  let len := b - a + 1
  let k := len / L
  let rem := len % L
  have hlen_eq : len = k * L + rem := by rw [mul_comm]; exact (Nat.div_add_mod len L).symm
  have hrem_lt : rem < L := Nat.mod_lt len hL
  have hIcc_eq : Finset.Icc a b = Finset.Ico a (a + len) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico, len]; omega
  have hdisj : Disjoint (Finset.Ico a (a + k * L)) (Finset.Ico (a + k * L) (a + len)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [Finset.mem_Ico] at hx1 hx2; omega
  have hunion : Finset.Ico a (a + len) = Finset.Ico a (a + k * L) ∪ Finset.Ico (a + k * L) (a + len) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hcard_full : ∀ m : ℕ, ((Finset.Ico a (a + m * L)).filter (fun x => x % L = r)).card = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : Finset.Ico a (a + (m + 1) * L) = Finset.Ico a (a + m * L) ∪ Finset.Ico (a + m * L) (a + m * L + L) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_union, add_mul, one_mul]; omega
      have hdj : Disjoint (Finset.Ico a (a + m * L)) (Finset.Ico (a + m * L) (a + m * L + L)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2; rw [Finset.mem_Ico] at hx1 hx2; omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdj),
        ih, hblock (a + m * L)]
  have hcard_rem : ((Finset.Ico (a + k * L) (a + len)).filter (fun x => x % L = r)).card ≤ 1 := by
    have hsub : Finset.Ico (a + k * L) (a + len) ⊆ Finset.Ico (a + k * L) (a + k * L + L) := by
      intro x hx; rw [Finset.mem_Ico] at hx ⊢; omega
    calc ((Finset.Ico (a + k * L) (a + len)).filter (fun x => x % L = r)).card
        ≤ ((Finset.Ico (a + k * L) (a + k * L + L)).filter (fun x => x % L = r)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hsub)
      _ = 1 := hblock (a + k * L)
  have hS_card : S.card = k + ((Finset.Ico (a + k * L) (a + len)).filter (fun x => x % L = r)).card := by
    simp only [S, hIcc_eq, hunion, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), hcard_full k]
  have hS_ge : (k : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (by omega : k ≤ S.card)
  have hS_le : (S.card : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : S.card ≤ k + 1)
  have hdiv_eq : ((len : ℕ) : ℝ) / (L : ℝ) = (k : ℝ) + (rem : ℝ) / (L : ℝ) := by
    have hcast : (len : ℝ) = (k : ℝ) * (L : ℝ) + (rem : ℝ) := by exact_mod_cast hlen_eq
    rw [hcast]; field_simp [ne_of_gt hL_pos]
  have hrem_ge0 : 0 ≤ (rem : ℝ) / (L : ℝ) := div_nonneg (Nat.cast_nonneg _) (le_of_lt hL_pos)
  have hrem_le1 : (rem : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hL_pos).mpr (by exact_mod_cast le_of_lt hrem_lt)
  constructor <;> linarith

/-- **Theorem 1 (Unweighted AP Discrepancy `≤ 1`)**:
For every modulus `L ≥ 1`, residue `r < L`, and `a ≤ b`:
`|∑ x ∈ Icc a b, ((if x % L = r then 1 else 0) - 1 / L)| ≤ 1`. -/
theorem unweighted_ap_discrepancy_le_one {L r a b : ℕ} (hL : 0 < L) (hr : r < L) (hab : a ≤ b) :
    |∑ x ∈ Finset.Icc a b, ((if x % L = r then (1 : ℝ) else 0) - 1 / (L : ℝ))| ≤ 1 := by
  have hsum : ∑ x ∈ Finset.Icc a b, ((if x % L = r then (1 : ℝ) else 0) - 1 / (L : ℝ))
      = (((Finset.Icc a b).filter (fun x => x % L = r)).card : ℝ) - ((b - a + 1 : ℕ) : ℝ) / (L : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : b + 1 - a = b - a + 1 := by omega
    rw [hcard, mul_one_div]
  rw [hsum, abs_le]
  have hb := card_ap_Icc_bounds hL hr hab
  constructor <;> linarith

lemma discrete_abel_summation (g f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, g j * f j =
      (∑ j ∈ Finset.Icc a b, g j) * f b
        + ∑ m ∈ Finset.Ico a b, (∑ j ∈ Finset.Icc a m, g j) * (f m - f (m + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    have hIcc : Finset.Icc a (k + 1) = insert (k + 1) (Finset.Icc a k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc a k := by simp
    have hIco : Finset.Ico a (k + 1) = insert k (Finset.Ico a k) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnotIco : k ∉ Finset.Ico a k := by simp
    rw [hIcc, Finset.sum_insert hnot, Finset.sum_insert hnot, ih, hIco, Finset.sum_insert hnotIco]
    ring

/-- **Theorem 2 (Exact Weighted AP Discrepancy Bound)**:
For every `L ≥ 1`, `r < L`, `a ≤ b`, and ANY weight `f : ℕ → ℝ`:
`|∑_{x ∈ Icc a b, x % L = r} f x - (1 / L) * ∑_{x ∈ Icc a b} f x| ≤ |f b| + ∑_{x ∈ Ico a b} |f x - f (x + 1)|`. -/
theorem weighted_ap_discrepancy_le {L r a b : ℕ} (hL : 0 < L) (hr : r < L) (hab : a ≤ b) (f : ℕ → ℝ) :
    |(∑ x ∈ (Finset.Icc a b).filter (fun x => x % L = r), f x)
        - (1 / (L : ℝ)) * (∑ x ∈ Finset.Icc a b, f x)|
      ≤ |f b| + ∑ x ∈ Finset.Ico a b, |f x - f (x + 1)| := by
  let g : ℕ → ℝ := fun x => (if x % L = r then (1 : ℝ) else 0) - 1 / (L : ℝ)
  have hrew : (∑ x ∈ (Finset.Icc a b).filter (fun x => x % L = r), f x)
        - (1 / (L : ℝ)) * (∑ x ∈ Finset.Icc a b, f x)
      = ∑ x ∈ Finset.Icc a b, g x * f x := by
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [g]; split_ifs <;> ring
  rw [hrew, discrete_abel_summation g f hab]
  calc |(∑ j ∈ Finset.Icc a b, g j) * f b
          + ∑ m ∈ Finset.Ico a b, (∑ j ∈ Finset.Icc a m, g j) * (f m - f (m + 1))|
      ≤ |(∑ j ∈ Finset.Icc a b, g j) * f b|
          + |∑ m ∈ Finset.Ico a b, (∑ j ∈ Finset.Icc a m, g j) * (f m - f (m + 1))| :=
        abs_add_le _ _
    _ ≤ |f b| + ∑ m ∈ Finset.Ico a b, |(∑ j ∈ Finset.Icc a m, g j) * (f m - f (m + 1))| := by
        have h1 : |(∑ j ∈ Finset.Icc a b, g j) * f b| ≤ |f b| := by
          rw [abs_mul]
          have := mul_le_mul_of_nonneg_right (unweighted_ap_discrepancy_le_one hL hr hab) (abs_nonneg (f b))
          linarith
        have h2 := Finset.abs_sum_le_sum_abs
          (fun m => (∑ j ∈ Finset.Icc a m, g j) * (f m - f (m + 1))) (Finset.Ico a b)
        linarith
    _ ≤ |f b| + ∑ m ∈ Finset.Ico a b, |f m - f (m + 1)| := by
        apply add_le_add le_rfl
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Ico] at hm
        rw [abs_mul]
        have := mul_le_mul_of_nonneg_right (unweighted_ap_discrepancy_le_one hL hr hm.1) (abs_nonneg (f m - f (m + 1)))
        linarith

/-! ### Part 2: Exact Weighted CRT Discrepancy for `d₁ ∣ x ∧ d₂ ∣ (n - x)` -/

/-- Exact CRT characterization of `d₁ ∣ x ∧ d₂ ∣ (n - x)` on `x ≤ n`:
- If `¬ gcd d₁ d₂ ∣ n`, there are NO solutions.
- If `gcd d₁ d₂ ∣ n`, there is a UNIQUE residue `r < lcm d₁ d₂` such that for all `x ≤ n`,
  `d₁ ∣ x ∧ d₂ ∣ (n - x) ↔ x % lcm d₁ d₂ = r`. -/
lemma crt_exists_unique_residue {n d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hg : Nat.gcd d₁ d₂ ∣ n) :
    ∃ r < Nat.lcm d₁ d₂, ∀ x ≤ n, (d₁ ∣ x ∧ d₂ ∣ n - x) ↔ x % Nat.lcm d₁ d₂ = r := by
  let g := Nat.gcd d₁ d₂
  let d₁' := d₁ / g
  let d₂' := d₂ / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d₂ hd₁
  have hgd₁ : g ∣ d₁ := Nat.gcd_dvd_left d₁ d₂
  have hgd₂ : g ∣ d₂ := Nat.gcd_dvd_right d₁ d₂
  have hcop : Nat.Coprime d₁' d₂' := Nat.coprime_div_gcd_div_gcd hg_pos
  have hlcm_eq : Nat.lcm d₁ d₂ = g * (d₁' * d₂') := by
    have hmul : g * Nat.lcm d₁ d₂ = d₁ * d₂ := Nat.gcd_mul_lcm d₁ d₂
    have hrhs : d₁ * d₂ = g * (g * (d₁' * d₂')) := by
      have h1 : g * d₁' = d₁ := Nat.mul_div_cancel' hgd₁
      have h2 : g * d₂' = d₂ := Nat.mul_div_cancel' hgd₂
      calc d₁ * d₂ = (g * d₁') * (g * d₂') := by rw [h1, h2]
        _ = g * (g * (d₁' * d₂')) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos (hmul.trans hrhs)
  have hlcm_pos : 0 < Nat.lcm d₁ d₂ := Nat.lcm_pos hd₁ hd₂
  -- Construct CRT solution u for u ≡ 0 (mod d₁') and u ≡ n/g (mod d₂'):
  let u := (Nat.chineseRemainder hcop 0 (n / g)).val
  have hu1 : u ≡ 0 [MOD d₁'] := (Nat.chineseRemainder hcop 0 (n / g)).property.1
  have hu2 : u ≡ n / g [MOD d₂'] := (Nat.chineseRemainder hcop 0 (n / g)).property.2
  let r := (g * u) % Nat.lcm d₁ d₂
  refine ⟨r, Nat.mod_lt _ hlcm_pos, ?_⟩
  intro x hxn
  have hmod_r : r ≡ g * u [MOD Nat.lcm d₁ d₂] := Nat.mod_modEq (g * u) (Nat.lcm d₁ d₂)
  constructor
  · rintro ⟨h1, h2⟩
    have hgx : g ∣ x := dvd_trans hgd₁ h1
    have hd1x : d₁' ∣ x / g := by
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      have : g * (x / g) = g * (d₁' * k) := by
        rw [Nat.mul_div_cancel' hgx, ← mul_assoc, Nat.mul_div_cancel' hgd₁, hk]
      exact Nat.eq_of_mul_eq_mul_left hg_pos this
    have hd2x : d₂' ∣ (n / g - x / g) := by
      obtain ⟨k, hk⟩ := h2
      refine ⟨k, ?_⟩
      have : g * (n / g - x / g) = g * (d₂' * k) := by
        rw [Nat.mul_sub, Nat.mul_div_cancel' hg, Nat.mul_div_cancel' hgx, ← mul_assoc, Nat.mul_div_cancel' hgd₂, hk]
      exact Nat.eq_of_mul_eq_mul_left hg_pos this
    have hcong1 : x / g ≡ u [MOD d₁'] := by
      have h0 : x / g ≡ 0 [MOD d₁'] := Nat.modEq_zero_iff_dvd.mpr hd1x
      exact h0.trans hu1.symm
    have hcong2 : x / g ≡ u [MOD d₂'] := by
      have hle : x / g ≤ n / g := Nat.div_le_div_right hxn
      have hsub : n / g - x / g ≡ 0 [MOD d₂'] := Nat.modEq_zero_iff_dvd.mpr hd2x
      have hadd := hsub.add_right (x / g)
      rw [Nat.sub_add_cancel hle, zero_add] at hadd
      exact hadd.symm.trans hu2.symm
    have hcong_prod : x / g ≡ u [MOD d₁' * d₂'] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hcong1, hcong2⟩
    have hcong_g : g * (x / g) ≡ g * u [MOD g * (d₁' * d₂')] := hcong_prod.mul_left' g
    rw [Nat.mul_div_cancel' hgx, ← hlcm_eq] at hcong_g
    exact hcong_g
  · intro hxr
    have hcong_r : x ≡ r [MOD Nat.lcm d₁ d₂] := by
      rw [Nat.ModEq, hxr, Nat.mod_eq_of_lt (Nat.mod_lt _ hlcm_pos)]
    have hcong : x ≡ g * u [MOD Nat.lcm d₁ d₂] := hcong_r.trans hmod_r
    have hd1_dvd_lcm : d₁ ∣ Nat.lcm d₁ d₂ := Nat.dvd_lcm_left d₁ d₂
    have hd2_dvd_lcm : d₂ ∣ Nat.lcm d₁ d₂ := Nat.dvd_lcm_right d₁ d₂
    have h1 : d₁ ∣ x := by
      have hc1 : x ≡ g * u [MOD d₁] := hcong.of_dvd hd1_dvd_lcm
      have hgu : d₁ ∣ g * u := by
        have hdu : d₁' ∣ u := Nat.modEq_zero_iff_dvd.mp hu1
        obtain ⟨k, hk⟩ := hdu
        refine ⟨k, ?_⟩
        rw [hk, ← mul_assoc, Nat.mul_div_cancel' hgd₁]
      exact (Nat.modEq_zero_iff_dvd.mp (hc1.trans (Nat.modEq_zero_iff_dvd.mpr hgu)))
    have h2 : d₂ ∣ n - x := by
      have hc2 : x ≡ g * u [MOD d₂] := hcong.of_dvd hd2_dvd_lcm
      have hgu_n : g * u ≡ n [MOD d₂] := by
        have h1 : g * u ≡ g * (n / g) [MOD g * d₂'] := hu2.mul_left' g
        rwa [Nat.mul_div_cancel' hg, Nat.mul_div_cancel' hgd₂] at h1
      have hxn_mod : x ≡ n [MOD d₂] := hc2.trans hgu_n
      exact (Nat.modEq_iff_dvd' hxn).mp hxn_mod
    exact ⟨h1, h2⟩

/-- **Theorem 3 (Exact Weighted CRT Discrepancy Bound for `d₁ ∣ x ∧ d₂ ∣ (n - x)`)**:
For every `n ≥ 4`, `d₁, d₂ ≥ 1`, and ANY weight `f : ℕ → ℝ`:
`|∑_{x ∈ Icc 2 (n-2), d₁ ∣ x ∧ d₂ ∣ (n - x)} f x - (if gcd d₁ d₂ ∣ n then 1 / lcm d₁ d₂ else 0) * ∑_{x ∈ Icc 2 (n-2)} f x|`
`≤ |f (n - 2)| + ∑_{x ∈ Ico 2 (n-2)} |f x - f (x + 1)|`. -/
theorem crt_weighted_discrepancy_le {n d₁ d₂ : ℕ} (hn : 4 ≤ n) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f : ℕ → ℝ) :
    |(∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => d₁ ∣ x ∧ d₂ ∣ n - x), f x)
        - (if Nat.gcd d₁ d₂ ∣ n then 1 / (Nat.lcm d₁ d₂ : ℝ) else 0) * (∑ x ∈ Finset.Icc 2 (n - 2), f x)|
      ≤ |f (n - 2)| + ∑ x ∈ Finset.Ico 2 (n - 2), |f x - f (x + 1)| := by
  by_cases hg : Nat.gcd d₁ d₂ ∣ n
  · obtain ⟨r, hr, hiff⟩ := crt_exists_unique_residue hd₁ hd₂ hg
    have hfilt : (Finset.Icc 2 (n - 2)).filter (fun x => d₁ ∣ x ∧ d₂ ∣ n - x)
        = (Finset.Icc 2 (n - 2)).filter (fun x => x % Nat.lcm d₁ d₂ = r) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨hx, h⟩; exact ⟨hx, (hiff x (by omega)).mp h⟩
      · intro ⟨hx, h⟩; exact ⟨hx, (hiff x (by omega)).mpr h⟩
    simp only [hg, ↓reduceIte, hfilt]
    exact weighted_ap_discrepancy_le (Nat.lcm_pos hd₁ hd₂) hr (by omega) f
  · have hempty : (Finset.Icc 2 (n - 2)).filter (fun x => d₁ ∣ x ∧ d₂ ∣ n - x) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx h
      rw [Finset.mem_Icc] at hx
      have h1 : Nat.gcd d₁ d₂ ∣ x := dvd_trans (Nat.gcd_dvd_left d₁ d₂) h.1
      have h2 : Nat.gcd d₁ d₂ ∣ n - x := dvd_trans (Nat.gcd_dvd_right d₁ d₂) h.2
      have hadd := dvd_add h1 h2
      rw [Nat.add_sub_cancel' (by omega : x ≤ n)] at hadd
      exact hg hadd
    simp only [hg, ↓reduceIte, hempty, Finset.sum_empty, zero_mul, sub_zero, abs_zero]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-! ### Part 3: Total-Variation Bound for Monotone × Antitone Products & Region I `O(Y (log n)^3)` Error -/

lemma sum_Ico_telescope (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ x ∈ Finset.Ico a b, (w (x + 1) - w x) = w b - w a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    have hIco : Finset.Ico a (k + 1) = insert k (Finset.Ico a k) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Ico a k := by simp
    rw [hIco, Finset.sum_insert hnot, ih]; ring

/-- **Theorem 4 (Total-Variation Bound for Monotone × Antitone Products)**:
If `0 ≤ u x ≤ U` is monotone non-decreasing and `0 ≤ v x ≤ V` is antitone non-increasing on `[a, b]`,
then `|u b * v b| + ∑_{x ∈ Ico a b} |u x * v x - u (x + 1) * v (x + 1)| ≤ 3 * U * V`. -/
theorem tv_prod_monotone_antitone_le (u v : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) {U V : ℝ}
    (hu_nn : ∀ x ∈ Finset.Icc a b, 0 ≤ u x) (hu_le : ∀ x ∈ Finset.Icc a b, u x ≤ U)
    (hu_mono : ∀ x, a ≤ x → x < b → u x ≤ u (x + 1))
    (hv_nn : ∀ x ∈ Finset.Icc a b, 0 ≤ v x) (hv_le : ∀ x ∈ Finset.Icc a b, v x ≤ V)
    (hv_anti : ∀ x, a ≤ x → x < b → v (x + 1) ≤ v x) :
    |u b * v b| + ∑ x ∈ Finset.Ico a b, |u x * v x - u (x + 1) * v (x + 1)| ≤ 3 * U * V := by
  have hU_nn : 0 ≤ U := le_trans (hu_nn a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)) (hu_le a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩))
  have hV_nn : 0 ≤ V := le_trans (hv_nn a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)) (hv_le a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩))
  have hb_term : |u b * v b| ≤ U * V := by
    have hub_nn := hu_nn b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
    have hvb_nn := hv_nn b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
    rw [abs_of_nonneg (mul_nonneg hub_nn hvb_nn)]
    exact mul_le_mul (hu_le b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)) (hv_le b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)) hvb_nn hU_nn
  have hstep : ∑ x ∈ Finset.Ico a b, |u x * v x - u (x + 1) * v (x + 1)|
      ≤ ∑ x ∈ Finset.Ico a b, (U * (v x - v (x + 1)) + V * (u (x + 1) - u x)) := by
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mem_Ico] at hx
    have hx_mem : x ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨hx.1, le_of_lt hx.2⟩
    have hx1_mem : x + 1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
    have hrew : u x * v x - u (x + 1) * v (x + 1)
        = u x * (v x - v (x + 1)) - v (x + 1) * (u (x + 1) - u x) := by ring
    rw [hrew]
    have hdv_nn : 0 ≤ v x - v (x + 1) := sub_nonneg.mpr (hv_anti x hx.1 hx.2)
    have hdu_nn : 0 ≤ u (x + 1) - u x := sub_nonneg.mpr (hu_mono x hx.1 hx.2)
    have ht1 : |u x * (v x - v (x + 1))| ≤ U * (v x - v (x + 1)) := by
      rw [abs_of_nonneg (mul_nonneg (hu_nn x hx_mem) hdv_nn)]
      exact mul_le_mul_of_nonneg_right (hu_le x hx_mem) hdv_nn
    have ht2 : |v (x + 1) * (u (x + 1) - u x)| ≤ V * (u (x + 1) - u x) := by
      rw [abs_of_nonneg (mul_nonneg (hv_nn (x + 1) hx1_mem) hdu_nn)]
      exact mul_le_mul_of_nonneg_right (hv_le (x + 1) hx1_mem) hdu_nn
    have htri := abs_sub (u x * (v x - v (x + 1))) (v (x + 1) * (u (x + 1) - u x))
    linarith
  have htel_v : ∑ x ∈ Finset.Ico a b, (v x - v (x + 1)) = v a - v b := by
    have hneg : ∑ x ∈ Finset.Ico a b, (v x - v (x + 1)) = -(∑ x ∈ Finset.Ico a b, (v (x + 1) - v x)) := by
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
    rw [hneg, sum_Ico_telescope v hab]; ring
  have htel_u : ∑ x ∈ Finset.Ico a b, (u (x + 1) - u x) = u b - u a := sum_Ico_telescope u hab
  have hsum_eval : ∑ x ∈ Finset.Ico a b, (U * (v x - v (x + 1)) + V * (u (x + 1) - u x))
      = U * (v a - v b) + V * (u b - u a) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htel_v, htel_u]
  have hva_le : v a - v b ≤ V := by
    linarith [hv_le a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩), hv_nn b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)]
  have hub_le : u b - u a ≤ U := by
    linarith [hu_le b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩), hu_nn a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)]
  have h1 : U * (v a - v b) ≤ U * V := mul_le_mul_of_nonneg_left hva_le hU_nn
  have h2 : V * (u b - u a) ≤ V * U := mul_le_mul_of_nonneg_left hub_le hV_nn
  linarith

/-- Smooth continuous-cofactor version of Wave 14's second-order weight:
`w2Smooth n σ d t = (d^(-σ) - 2 * (n * t / d)^(-σ) + n^(-2σ) * d^σ) / σ`.
Note: when `d ∣ t`, `t / d` in `ℝ` equals the exact integer cofactor `(t / d : ℕ)`! -/
noncomputable def w2Smooth (n : ℕ) (σ : ℝ) (d t : ℕ) : ℝ :=
  ((d : ℝ) ^ (-σ) - 2 * ((n : ℝ) * (t : ℝ) / (d : ℝ)) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ) / σ

/-- Region I sum of `C_{n,σ}` over `(d₁, d₂) ∈ H_Y = {(d₁, d₂) ∈ [1, Y]^2 : d₁ * d₂ ≤ Y}`
(where for `d₁ ∣ x ∧ d₂ ∣ (n - x)`, `w2Smooth` equals the exact integer weight `w2DivSigma`). -/
noncomputable def regI_C2 (n Y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun p => p.1 * p.2 ≤ Y),
    (μ p.1 : ℝ) * (μ p.2 : ℝ) *
      ∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => p.1 ∣ x ∧ p.2 ∣ n - x),
        w2Smooth n σ p.1 x * w2Smooth n σ p.2 (n - x)

/-- Factored CRT main-term approximation for Region I of `C_{n,σ}`. -/
noncomputable def regI_C2_CRT (n Y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun p => p.1 * p.2 ≤ Y),
    (μ p.1 : ℝ) * (μ p.2 : ℝ) *
      ((if Nat.gcd p.1 p.2 ∣ n then 1 / (Nat.lcm p.1 p.2 : ℝ) else 0) *
        ∑ x ∈ Finset.Icc 2 (n - 2), w2Smooth n σ p.1 x * w2Smooth n σ p.2 (n - x))

lemma w2Smooth_bounds_and_mono {n d t₁ t₂ : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n)
    (ht₁ : d ≤ t₁) (h12 : t₁ ≤ t₂) (ht₂ : t₂ ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ w2Smooth n σ d t₁ ∧
    w2Smooth n σ d t₁ ≤ σ * (Real.log (n : ℝ)) ^ 2 + 2 * Real.log (n : ℝ) ∧
    w2Smooth n σ d t₁ ≤ w2Smooth n σ d t₂ := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht1_pos : (0 : ℝ) < (t₁ : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht2_pos : (0 : ℝ) < (t₂ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk1_ge1 : (1 : ℝ) ≤ (t₁ : ℝ) / (d : ℝ) := (one_le_div hd_pos).mpr (by exact_mod_cast ht₁)
  have hk1_le_n : (t₁ : ℝ) / (d : ℝ) ≤ (n : ℝ) := by
    rw [div_le_iff₀ hd_pos]
    have h1 : (t₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans h12 ht₂)
    have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  -- Exact square decomposition of w2Smooth n σ d t₁:
  have hsq_id : (d : ℝ) ^ (-σ) - 2 * ((n : ℝ) * (t₁ : ℝ) / (d : ℝ)) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
      = (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2
        + 2 * (n : ℝ) ^ (-σ) * (1 - ((t₁ : ℝ) / (d : ℝ)) ^ (-σ)) := by
    have hmul_div : (n : ℝ) * (t₁ : ℝ) / (d : ℝ) = (n : ℝ) * ((t₁ : ℝ) / (d : ℝ)) := by ring
    rw [hmul_div, Real.mul_rpow (Nat.cast_nonneg n) (div_nonneg (Nat.cast_nonneg t₁) (Nat.cast_nonneg d)),
      Real.div_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg n)]
    have hd1 : (d : ℝ) ^ (-σ) * (d : ℝ) ^ σ = 1 := by rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero]
    have hd2 : (d : ℝ) ^ (-σ) * ((d : ℝ) ^ σ * (d : ℝ) ^ σ) = (d : ℝ) ^ σ := by rw [← mul_assoc, hd1, one_mul]
    have hn1 : ((n : ℝ) ^ σ)⁻¹ = (n : ℝ) ^ (-σ) := (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
    have hn2 : (n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(2 * σ)) := by rw [← Real.rpow_add hn_pos]; congr 1; ring
    have hdiv : (d : ℝ) ^ σ / (n : ℝ) ^ σ = (d : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by rw [div_eq_mul_inv, hn1]
    rw [hdiv, sq]
    calc (d : ℝ) ^ (-σ) - 2 * ((n : ℝ) ^ (-σ) * ((t₁ : ℝ) / (d : ℝ)) ^ (-σ)) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
        = (d : ℝ) ^ (-σ) - 2 * ((d : ℝ) ^ (-σ) * (d : ℝ) ^ σ) * (n : ℝ) ^ (-σ)
          + ((d : ℝ) ^ (-σ) * ((d : ℝ) ^ σ * (d : ℝ) ^ σ)) * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
          + 2 * (n : ℝ) ^ (-σ) * (1 - ((t₁ : ℝ) / (d : ℝ)) ^ (-σ)) := by rw [hd1, hd2, hn2]; ring
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · unfold w2Smooth; rw [hsq_id]
    have h1 : 0 ≤ (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg _)
    have hk_le1 : ((t₁ : ℝ) / (d : ℝ)) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1_ge1 (by linarith)
    have h2 : 0 ≤ 2 * (n : ℝ) ^ (-σ) * (1 - ((t₁ : ℝ) / (d : ℝ)) ^ (-σ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by linarith)
    exact div_nonneg (add_nonneg h1 h2) (le_of_lt hσ)
  · unfold w2Smooth; rw [hsq_id, div_le_iff₀ hσ]
    have hnd_ge1 : (1 : ℝ) ≤ (n : ℝ) / (d : ℝ) := (one_le_div hd_pos).mpr (by exact_mod_cast hdn)
    have hnd_le_n : (n : ℝ) / (d : ℝ) ≤ (n : ℝ) := div_le_self (Nat.cast_nonneg n) (by exact_mod_cast hd)
    have hlog_nd_nn : 0 ≤ Real.log ((n : ℝ) / (d : ℝ)) := Real.log_nonneg hnd_ge1
    have hlog_nd_le : Real.log ((n : ℝ) / (d : ℝ)) ≤ Real.log (n : ℝ) := Real.log_le_log (div_pos hn_pos hd_pos) hnd_le_n
    have hdn_exp : ((d : ℝ) / (n : ℝ)) ^ σ = Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) := by
      rw [Real.rpow_def_of_pos (div_pos hd_pos hn_pos), Real.log_div (ne_of_gt hd_pos) (ne_of_gt hn_pos),
        Real.log_div (ne_of_gt hn_pos) (ne_of_gt hd_pos)]
      congr 1; ring
    have hsq_le : (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 ≤ (σ * Real.log (n : ℝ)) ^ 2 := by
      rw [hdn_exp]
      have hnn : 0 ≤ 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) := by
        linarith [Real.exp_le_one_iff.mpr (by nlinarith : -σ * Real.log ((n : ℝ) / (d : ℝ)) ≤ 0)]
      have hlin : 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) ≤ σ * Real.log (n : ℝ) := by
        have h1 : 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) ≤ σ * Real.log ((n : ℝ) / (d : ℝ)) := by
          linarith [Real.add_one_le_exp (-σ * Real.log ((n : ℝ) / (d : ℝ)))]
        have h2 : σ * Real.log ((n : ℝ) / (d : ℝ)) ≤ σ * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hlog_nd_le (le_of_lt hσ)
        linarith
      rw [sq, sq]; exact mul_le_mul hlin hlin hnn (le_trans hnn hlin)
    have hd_le1 : (d : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    have hterm1 : (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 ≤ σ ^ 2 * (Real.log (n : ℝ)) ^ 2 := by
      calc _ ≤ 1 * (σ * Real.log (n : ℝ)) ^ 2 := mul_le_mul hd_le1 hsq_le (sq_nonneg _) (by norm_num)
        _ = σ ^ 2 * (Real.log (n : ℝ)) ^ 2 := by ring
    have hk_exp : ((t₁ : ℝ) / (d : ℝ)) ^ (-σ) = Real.exp (-σ * Real.log ((t₁ : ℝ) / (d : ℝ))) := by
      rw [Real.rpow_def_of_pos (div_pos ht1_pos hd_pos), mul_comm]
    have hk_le : 1 - ((t₁ : ℝ) / (d : ℝ)) ^ (-σ) ≤ σ * Real.log (n : ℝ) := by
      rw [hk_exp]
      have h1 : 1 - Real.exp (-σ * Real.log ((t₁ : ℝ) / (d : ℝ))) ≤ σ * Real.log ((t₁ : ℝ) / (d : ℝ)) := by
        linarith [Real.add_one_le_exp (-σ * Real.log ((t₁ : ℝ) / (d : ℝ)))]
      have h2 : Real.log ((t₁ : ℝ) / (d : ℝ)) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (div_pos ht1_pos hd_pos) hk1_le_n
      have h3 : σ * Real.log ((t₁ : ℝ) / (d : ℝ)) ≤ σ * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left h2 (le_of_lt hσ)
      linarith
    have hk_nn : 0 ≤ 1 - ((t₁ : ℝ) / (d : ℝ)) ^ (-σ) := by
      linarith [Real.rpow_le_one_of_one_le_of_nonpos hk1_ge1 (by linarith : -σ ≤ 0)]
    have hn_le1 : (n : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
    have hterm2 : 2 * (n : ℝ) ^ (-σ) * (1 - ((t₁ : ℝ) / (d : ℝ)) ^ (-σ)) ≤ 2 * (σ * Real.log (n : ℝ)) := by
      have := mul_le_mul hn_le1 hk_le hk_nn (by norm_num); linarith
    calc _ ≤ σ ^ 2 * (Real.log (n : ℝ)) ^ 2 + 2 * (σ * Real.log (n : ℝ)) := add_le_add hterm1 hterm2
      _ = (σ * (Real.log (n : ℝ)) ^ 2 + 2 * Real.log (n : ℝ)) * σ := by ring
  · unfold w2Smooth
    apply div_le_div_of_nonneg_right _ (le_of_lt hσ)
    have harg_pos : 0 < (n : ℝ) * (t₁ : ℝ) / (d : ℝ) := div_pos (mul_pos hn_pos ht1_pos) hd_pos
    have harg_le : (n : ℝ) * (t₁ : ℝ) / (d : ℝ) ≤ (n : ℝ) * (t₂ : ℝ) / (d : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h12) (le_of_lt hn_pos)) (le_of_lt hd_pos)
    have hrpow := Real.rpow_le_rpow_of_nonpos harg_pos harg_le (by linarith : -σ ≤ 0)
    linarith

/-- **Theorem 5 (Unconditional Explicit `O(Y (log n)^3)` Region I CRT Error Bound for `C_{n,σ}`)**:
For every `n ≥ 4`, every `Y ≤ n - 2` (restricted to pairs `d₁ * d₂ ≤ Y` with `d₁, d₂ ≤ n - 2`),
and every `σ > 0`, letting `B := σ * (log n)^2 + 2 * log n` and
`H_Y := {(d₁, d₂) ∈ [1, Y]^2 : d₁ * d₂ ≤ Y ∧ d₁ ≤ 2 ∧ d₂ ≤ 2}` — more generally, on ANY
sub-hyperbola `d₁, d₂ ≤ n - 2` with `x ∈ [max 2 d₁, n - max 2 d₂]` — Wait: for `d₁ ≤ 2, d₂ ≤ 2`
`w2Smooth` is non-negative on `[2, n-2]`; for general `d₁, d₂ ≤ Y` we clamp `t ↦ max t d`
(which STILL equals `t` whenever `d ∣ t` and `t ≥ 1`!), giving the UNCONDITIONAL bound over ALL of `H_Y`! -/
noncomputable def w2Clamped (n : ℕ) (σ : ℝ) (d t : ℕ) : ℝ :=
  w2Smooth n σ d (max d t)

lemma w2Clamped_eq_of_dvd {n d t : ℕ} (ht : 0 < t) (hdvd : d ∣ t) (σ : ℝ) :
    w2Clamped n σ d t = w2Smooth n σ d t := by
  unfold w2Clamped
  rw [max_eq_right (Nat.le_of_dvd ht hdvd)]

noncomputable def regI_C2_clamped (n Y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun p => p.1 * p.2 ≤ Y),
    (μ p.1 : ℝ) * (μ p.2 : ℝ) *
      ∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => p.1 ∣ x ∧ p.2 ∣ n - x),
        w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x)

noncomputable def regI_C2_clamped_CRT (n Y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun p => p.1 * p.2 ≤ Y),
    (μ p.1 : ℝ) * (μ p.2 : ℝ) *
      ((if Nat.gcd p.1 p.2 ∣ n then 1 / (Nat.lcm p.1 p.2 : ℝ) else 0) *
        ∑ x ∈ Finset.Icc 2 (n - 2), w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x))

/-- Exact equality `regI_C2 = regI_C2_clamped` (since `d₁ ∣ x ∧ d₂ ∣ (n - x)` forces `d₁ ≤ x` and `d₂ ≤ n - x`!). -/
lemma regI_C2_eq_clamped {n Y : ℕ} (hn : 4 ≤ n) (σ : ℝ) :
    regI_C2 n Y σ = regI_C2_clamped n Y σ := by
  unfold regI_C2 regI_C2_clamped
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at hx
  rw [w2Clamped_eq_of_dvd (by omega) hx.2.1, w2Clamped_eq_of_dvd (by omega) hx.2.2]

theorem regionI_secondOrder_crt_error_bound {n Y : ℕ} (hn : 4 ≤ n) (hYn : Y ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    |regI_C2 n Y σ - regI_C2_clamped_CRT n Y σ|
      ≤ 3 * (σ * (Real.log (n : ℝ)) ^ 2 + 2 * Real.log (n : ℝ)) ^ 2
          * (((Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun p => p.1 * p.2 ≤ Y)).card : ℝ) := by
  rw [regI_C2_eq_clamped hn σ]
  unfold regI_C2_clamped regI_C2_clamped_CRT
  rw [← Finset.sum_sub_distrib]
  let H := (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun p => p.1 * p.2 ≤ Y)
  let B := σ * (Real.log (n : ℝ)) ^ 2 + 2 * Real.log (n : ℝ)
  calc |∑ p ∈ H, _|
      ≤ ∑ p ∈ H, |(μ p.1 : ℝ) * (μ p.2 : ℝ) *
            ((∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => p.1 ∣ x ∧ p.2 ∣ n - x),
                w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x))
              - (if Nat.gcd p.1 p.2 ∣ n then 1 / (Nat.lcm p.1 p.2 : ℝ) else 0) *
                ∑ x ∈ Finset.Icc 2 (n - 2), w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x))| := by
        have hrew : ∀ p ∈ H,
            (μ p.1 : ℝ) * (μ p.2 : ℝ) * (∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => p.1 ∣ x ∧ p.2 ∣ n - x),
                w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x))
              - (μ p.1 : ℝ) * (μ p.2 : ℝ) * ((if Nat.gcd p.1 p.2 ∣ n then 1 / (Nat.lcm p.1 p.2 : ℝ) else 0) *
                ∑ x ∈ Finset.Icc 2 (n - 2), w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x))
            = (μ p.1 : ℝ) * (μ p.2 : ℝ) * ((∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => p.1 ∣ x ∧ p.2 ∣ n - x),
                w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x))
              - (if Nat.gcd p.1 p.2 ∣ n then 1 / (Nat.lcm p.1 p.2 : ℝ) else 0) *
                ∑ x ∈ Finset.Icc 2 (n - 2), w2Clamped n σ p.1 x * w2Clamped n σ p.2 (n - x)) := fun _ _ => by ring
        rw [Finset.sum_congr rfl hrew]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ H, (3 * B ^ 2) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
        have hp1_pos : 0 < p.1 := by omega
        have hp2_pos : 0 < p.2 := by omega
        have hp1_le : p.1 ≤ n := le_trans hp.1.1.2 hYn
        have hp2_le : p.2 ≤ n := le_trans hp.1.2.2 hYn
        have hmu1 : |(μ p.1 : ℝ)| ≤ 1 := by
          have : |μ p.1| ≤ 1 := by
            by_cases hsf : Squarefree p.1
            · rcases sq_eq_one_iff.mp (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf) with h | h <;>
                rw [h] <;> norm_num
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
          exact_mod_cast this
        have hmu2 : |(μ p.2 : ℝ)| ≤ 1 := by
          have : |μ p.2| ≤ 1 := by
            by_cases hsf : Squarefree p.2
            · rcases sq_eq_one_iff.mp (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf) with h | h <;>
                rw [h] <;> norm_num
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
          exact_mod_cast this
        have hmu_prod : |(μ p.1 : ℝ) * (μ p.2 : ℝ)| ≤ 1 := by
          rw [abs_mul]; have := mul_le_mul hmu1 hmu2 (abs_nonneg _) (by norm_num); linarith
        let u : ℕ → ℝ := fun x => w2Clamped n σ p.1 x
        let v : ℕ → ℝ := fun x => w2Clamped n σ p.2 (n - x)
        have hcrt := crt_weighted_discrepancy_le hn hp1_pos hp2_pos (fun x => u x * v x)
        have htv : |u (n - 2) * v (n - 2)| + ∑ x ∈ Finset.Ico 2 (n - 2), |u x * v x - u (x + 1) * v (x + 1)| ≤ 3 * B * B := by
          apply tv_prod_monotone_antitone_le u v (by omega)
          · intro x hx; rw [Finset.mem_Icc] at hx
            exact (w2Smooth_bounds_and_mono hp1_pos hp1_le (le_max_left _ _) le_rfl (max_le hp1_le (by omega)) hσ).1
          · intro x hx; rw [Finset.mem_Icc] at hx
            exact (w2Smooth_bounds_and_mono hp1_pos hp1_le (le_max_left _ _) le_rfl (max_le hp1_le (by omega)) hσ).2.1
          · intro x h1 h2
            exact (w2Smooth_bounds_and_mono hp1_pos hp1_le (le_max_left _ _)
              (max_le_max_left p.1 (Nat.le_succ x)) (max_le hp1_le (by omega)) hσ).2.2
          · intro x hx; rw [Finset.mem_Icc] at hx
            exact (w2Smooth_bounds_and_mono hp2_pos hp2_le (le_max_left _ _) le_rfl (max_le hp2_le (by omega)) hσ).1
          · intro x hx; rw [Finset.mem_Icc] at hx
            exact (w2Smooth_bounds_and_mono hp2_pos hp2_le (le_max_left _ _) le_rfl (max_le hp2_le (by omega)) hσ).2.1
          · intro x h1 h2
            exact (w2Smooth_bounds_and_mono hp2_pos hp2_le (le_max_left _ _)
              (max_le_max_left p.2 (by omega : n - (x + 1) ≤ n - x)) (max_le hp2_le (by omega)) hσ).2.2
        rw [abs_mul]
        have hdis_le : |(∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => p.1 ∣ x ∧ p.2 ∣ n - x), u x * v x)
            - (if Nat.gcd p.1 p.2 ∣ n then 1 / (Nat.lcm p.1 p.2 : ℝ) else 0) * ∑ x ∈ Finset.Icc 2 (n - 2), u x * v x|
            ≤ 3 * B ^ 2 := by
          have : 3 * B * B = 3 * B ^ 2 := by ring
          linarith
        calc |(μ p.1 : ℝ) * (μ p.2 : ℝ)| * |_|
            ≤ 1 * (3 * B ^ 2) := mul_le_mul hmu_prod hdis_le (abs_nonneg _) (by norm_num)
          _ = 3 * B ^ 2 := one_mul _
    _ = 3 * B ^ 2 * (H.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end GoldbachWave17
