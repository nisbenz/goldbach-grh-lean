import Mathlib

/-!
# Wave 10: Exact 3-Region Hyperbola Decomposition, CRT Discretization & BV Exponent Theorem

This file formalizes the exact 3-region hyperbola decomposition of the Wave 9
anti-symmetric bilateral Euler-product difference `4 * (Ξ_n^J(σ₁) - Ξ_n^J(σ₂))`
into:
- **Region I** (`d₁ * d₂ ≤ Y`, e.g. `Y = ⌊n^0.95⌋`): 100% elementary CRT.
- **Region II** (`d₁ * d₂ > Y ∧ (d₁ ≤ D ∨ d₂ ≤ D)`, e.g. `D = ⌊n^0.30⌋`):
  single long Möbius variable in arithmetic progressions, strictly inside the
  unconditional Bombieri–Vinogradov range `q < (X')^(1/2)`.
- **Region III** (`d₁ * d₂ > Y ∧ D < d₁ ∧ D < d₂`): the isolated open binary
  Möbius correlation core.

Every theorem below is unconditional, complete, and kernel-checked with only
standard axioms `[propext, Classical.choice, Quot.sound]`:
1. `three_region_split`: exact algebraic partition `4*(Ξ_n^J(σ₁) - Ξ_n^J(σ₂)) = RegI + RegII + RegIII`.
2. `crtPairCount_eq_zero_of_not_dvd` & `crtPairCount_approx`: exact elementary CRT bound
   `|(N_n°(d₁, d₂) : ℝ) - n / lcm(d₁, d₂)| ≤ 4` whenever `gcd(d₁, d₂) ∣ n`.
3. `gcd_dvd_indicator_eq_sum_psi`: exact multiplicative factorization
   `(if gcd d₁ d₂ ∣ n then gcd d₁ d₂ else 0) = ∑ h ∈ (gcd d₁ d₂).divisors, ψ_n(h)`
   for squarefree `d₁, d₂`, turning the Region I double CRT sum into a 1-variable
   product over `h` whose infinite limit yields the exact Hardy–Littlewood singular series `S(n)`.
4. `regionII_bv_modulus_bound`: exact arithmetic proof that every quadruple
   `d₁ * k₁ + d₂ * k₂ = n` in Region II (`d₁ ≤ D`, `Y < d₁ * d₂`) with
   `g = gcd k₂ d₁`, `h = gcd (n / g) (d₁ / g)`, reduced modulus `q = d₁ / (g * h)`
   satisfies `q^2 * (k₂ * h) * Y < D^3 * n`, placing Region II strictly inside
   unconditional Bombieri–Vinogradov (`q < (X')^(1/2)`) whenever `D^3 < Y` (e.g. `D = n^0.30, Y = n^0.95`).
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachWave10

/-! ### Part 1: Exact 3-Region Hyperbola Decomposition of `4 * (Ξ_n^J(σ₁) - Ξ_n^J(σ₂))` -/

/-- Anti-symmetric divisor weight for a single divisor `d` of `x` at parameter `σ`:
`μ(d) * (d^(-σ) - (x / d)^(-σ)) / σ`. -/
noncomputable def antiSymTerm (σ : ℝ) (x d : ℕ) : ℝ :=
  (μ d : ℝ) * ((d : ℝ) ^ (-σ) - ((x / d : ℕ) : ℝ) ^ (-σ)) / σ

/-- Sum of `antiSymTerm` over all divisors `d ∣ x`. -/
noncomputable def antiSymDivSum (σ : ℝ) (x : ℕ) : ℝ :=
  ∑ d ∈ x.divisors, antiSymTerm σ x d

/-- Bilateral anti-symmetric difference `4 * (Ξ_n^J(σ₁) - Ξ_n^J(σ₂))`. -/
noncomputable def bilateralDiff (n : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    (antiSymDivSum σ₁ x * antiSymDivSum σ₁ (n - x)
      - antiSymDivSum σ₂ x * antiSymDivSum σ₂ (n - x))

/-- Per-pair contribution at `(x, d₁, d₂)` where `d₁ ∣ x` and `d₂ ∣ (n - x)`. -/
noncomputable def pairDiffTerm (n : ℕ) (σ₁ σ₂ : ℝ) (x d₁ d₂ : ℕ) : ℝ :=
  antiSymTerm σ₁ x d₁ * antiSymTerm σ₁ (n - x) d₂
    - antiSymTerm σ₂ x d₁ * antiSymTerm σ₂ (n - x) d₂

/-- Region I (`d₁ * d₂ ≤ Y`): elementary CRT region. -/
noncomputable def regionI (n Y : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    ∑ p ∈ (x.divisors ×ˢ (n - x).divisors).filter (fun p => p.1 * p.2 ≤ Y),
      pairDiffTerm n σ₁ σ₂ x p.1 p.2

/-- Region II (`Y < d₁ * d₂ ∧ (d₁ ≤ D ∨ d₂ ≤ D)`): unconditional Bombieri–Vinogradov region for `μ`. -/
noncomputable def regionII (n Y D : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    ∑ p ∈ (x.divisors ×ˢ (n - x).divisors).filter (fun p => Y < p.1 * p.2 ∧ (p.1 ≤ D ∨ p.2 ≤ D)),
      pairDiffTerm n σ₁ σ₂ x p.1 p.2

/-- Region III (`Y < d₁ * d₂ ∧ D < d₁ ∧ D < d₂`): isolated open binary Möbius correlation core. -/
noncomputable def regionIII (n Y D : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    ∑ p ∈ (x.divisors ×ˢ (n - x).divisors).filter (fun p => Y < p.1 * p.2 ∧ D < p.1 ∧ D < p.2),
      pairDiffTerm n σ₁ σ₂ x p.1 p.2

/-- **Theorem 1 (Exact 3-Region Hyperbola Split)**:
For every `n, Y, D : ℕ` and every `σ₁, σ₂ : ℝ`,
`bilateralDiff n σ₁ σ₂ = regionI n Y σ₁ σ₂ + regionII n Y D σ₁ σ₂ + regionIII n Y D σ₁ σ₂`. -/
theorem three_region_split (n Y D : ℕ) (σ₁ σ₂ : ℝ) :
    bilateralDiff n σ₁ σ₂ =
      regionI n Y σ₁ σ₂ + regionII n Y D σ₁ σ₂ + regionIII n Y D σ₁ σ₂ := by
  classical
  unfold bilateralDiff regionI regionII regionIII
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  have hprod : antiSymDivSum σ₁ x * antiSymDivSum σ₁ (n - x)
        - antiSymDivSum σ₂ x * antiSymDivSum σ₂ (n - x)
      = ∑ p ∈ x.divisors ×ˢ (n - x).divisors, pairDiffTerm n σ₁ σ₂ x p.1 p.2 := by
    unfold antiSymDivSum pairDiffTerm
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.sum_product',
      ← Finset.sum_sub_distrib]
  rw [hprod]
  let U := x.divisors ×ˢ (n - x).divisors
  let f : ℕ × ℕ → ℝ := fun p => pairDiffTerm n σ₁ σ₂ x p.1 p.2
  have h1 := (Finset.sum_filter_add_sum_filter_not U (fun p => p.1 * p.2 ≤ Y) f).symm
  have h2 := (Finset.sum_filter_add_sum_filter_not
    (U.filter (fun p => ¬p.1 * p.2 ≤ Y)) (fun p => p.1 ≤ D ∨ p.2 ≤ D) f).symm
  rw [h1, h2]
  have hf2 : (U.filter (fun p => ¬p.1 * p.2 ≤ Y)).filter (fun p => p.1 ≤ D ∨ p.2 ≤ D)
      = U.filter (fun p => Y < p.1 * p.2 ∧ (p.1 ≤ D ∨ p.2 ≤ D)) := by
    ext p; simp [Finset.mem_filter, not_le, and_assoc]
  have hf3 : (U.filter (fun p => ¬p.1 * p.2 ≤ Y)).filter (fun p => ¬(p.1 ≤ D ∨ p.2 ≤ D))
      = U.filter (fun p => Y < p.1 * p.2 ∧ D < p.1 ∧ D < p.2) := by
    ext p; simp [Finset.mem_filter, not_le, not_or, and_assoc]
  rw [hf2, hf3]
  ring

/-! ### Part 2: Elementary CRT Congruence Count Error Bound (`|N_n°(d₁, d₂) - n / lcm(d₁, d₂)| ≤ 3`) -/

/-- Congruence count `N_n°(d₁, d₂) = #{x ∈ [2, n - 2] : d₁ ∣ x ∧ d₂ ∣ (n - x)}`. -/
def crtPairCount (n d₁ d₂ : ℕ) : ℕ :=
  ((Finset.Icc 2 (n - 2)).filter (fun x => d₁ ∣ x ∧ d₂ ∣ (n - x))).card

/-- If `gcd d₁ d₂` does not divide `n`, then `crtPairCount n d₁ d₂ = 0`. -/
theorem crtPairCount_eq_zero_of_not_dvd {n d₁ d₂ : ℕ} (hnd : ¬(Nat.gcd d₁ d₂ ∣ n)) :
    crtPairCount n d₁ d₂ = 0 := by
  unfold crtPairCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx ⟨hd₁, hd₂⟩
  rw [Finset.mem_Icc] at hx
  have hg1 : Nat.gcd d₁ d₂ ∣ x := dvd_trans (Nat.gcd_dvd_left d₁ d₂) hd₁
  have hg2 : Nat.gcd d₁ d₂ ∣ (n - x) := dvd_trans (Nat.gcd_dvd_right d₁ d₂) hd₂
  have hsum : x + (n - x) = n := by omega
  have hgn : Nat.gcd d₁ d₂ ∣ n := hsum ▸ dvd_add hg1 hg2
  exact hnd hgn

/-- Helper: count of `x ∈ Ico 0 n` with `x ≡ a [MOD L]` is bounded between `n / L` and `n / L + 1`. -/
lemma card_mod_Ico_bounds {n L a : ℕ} (hL : 0 < L) :
    n / L ≤ ((Finset.range n).filter (fun x => x % L = a % L)).card ∧
      ((Finset.range n).filter (fun x => x % L = a % L)).card ≤ n / L + 1 := by
  classical
  let r := a % L
  have hr : r < L := Nat.mod_lt a hL
  let S := (Finset.range n).filter (fun x => x % L = r)
  -- Map k ↦ k * L + r
  have hinj : Function.Injective (fun k : ℕ => k * L + r) := by
    intro k₁ k₂ h
    dsimp only at h
    have : k₁ * L = k₂ * L := by omega
    exact Nat.eq_of_mul_eq_mul_right hL this
  constructor
  · -- Lower bound: every k ∈ range (n / L) gives k * L + r ∈ S
    have hsub : (Finset.range (n / L)).image (fun k => k * L + r) ⊆ S := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have h1 : (k + 1) * L ≤ (n / L) * L := Nat.mul_le_mul_right L hk
        have h2 : (n / L) * L ≤ n := Nat.div_mul_le_self n L
        have h3 : (k + 1) * L = k * L + L := by ring
        omega
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]
    calc n / L = (Finset.range (n / L)).card := (Finset.card_range _).symm
      _ = ((Finset.range (n / L)).image (fun k => k * L + r)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ S.card := Finset.card_le_card hsub
  · -- Upper bound: every x ∈ S equals (x / L) * L + r with x / L < n / L + 1
    have hsub : S ⊆ (Finset.range (n / L + 1)).image (fun k => k * L + r) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      rw [Finset.mem_image]
      refine ⟨x / L, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hle : x / L ≤ n / L := Nat.div_le_div_right (le_of_lt hx.1)
        omega
      · have hdiv := Nat.div_add_mod x L
        rw [hx.2] at hdiv
        linarith [mul_comm L (x / L)]
    calc S.card ≤ ((Finset.range (n / L + 1)).image (fun k => k * L + r)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.range (n / L + 1)).card := Finset.card_image_le
      _ = n / L + 1 := Finset.card_range _

/-- **Theorem 2 (Elementary CRT Discretization Bound for Region I)**:
For every `n ≥ 4` and every `d₁, d₂ ≥ 1` with `gcd(d₁, d₂) ∣ n`,
`|(crtPairCount n d₁ d₂ : ℝ) - (n : ℝ) / (Nat.lcm d₁ d₂ : ℝ)| ≤ 4`. -/
theorem crtPairCount_approx {n d₁ d₂ : ℕ} (hn : 4 ≤ n) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hg : Nat.gcd d₁ d₂ ∣ n) :
    |(crtPairCount n d₁ d₂ : ℝ) - (n : ℝ) / (Nat.lcm d₁ d₂ : ℝ)| ≤ 4 := by
  classical
  set g := Nat.gcd d₁ d₂ with hg_def
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d₂ hd₁
  set d₁' := d₁ / g
  set d₂' := d₂ / g
  set n' := n / g
  have hd₁_eq : d₁ = g * d₁' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d₁ d₂)).symm
  have hd₂_eq : d₂ = g * d₂' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d₁ d₂)).symm
  have hn_eq : n = g * n' := (Nat.mul_div_cancel' hg).symm
  have hcop : Nat.Coprime d₁' d₂' := Nat.coprime_div_gcd_div_gcd hg_pos
  set L := Nat.lcm d₁ d₂ with hL_def
  have hL_pos : 0 < L := Nat.lcm_pos hd₁ hd₂
  have hL_eq : L = g * (d₁' * d₂') := by
    have hmul := Nat.gcd_mul_lcm d₁ d₂
    rw [← hg_def, ← hL_def] at hmul
    have h1 : g * (g * (d₁' * d₂')) = d₁ * d₂ := by
      rw [hd₁_eq, hd₂_eq]; ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos (hmul.trans h1.symm)
  -- Find a CRT representative a₀ such that d₁ ∣ a₀ and a₀ ≡ n [MOD d₂]
  let a₀ : ℕ := g * (Nat.chineseRemainder hcop 0 n').val
  have ha₀_d₁ : d₁ ∣ a₀ := by
    have h0 : d₁' ∣ (Nat.chineseRemainder hcop 0 n').val := by
      have hm := (Nat.chineseRemainder hcop 0 n').property.1
      rw [Nat.ModEq, Nat.zero_mod] at hm
      exact Nat.dvd_of_mod_eq_zero hm
    rw [hd₁_eq]
    exact Nat.mul_dvd_mul_left g h0
  have ha₀_d₂ : a₀ ≡ n [MOD d₂] := by
    have hm : (Nat.chineseRemainder hcop 0 n').val ≡ n' [MOD d₂'] :=
      (Nat.chineseRemainder hcop 0 n').property.2
    rw [hd₂_eq, hn_eq]
    have hzd : (d₂' : ℤ) ∣ (n' : ℤ) - ((Nat.chineseRemainder hcop 0 n').val : ℤ) :=
      Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hm)
    have hzg : ((g * d₂' : ℕ) : ℤ) ∣ ((g * n' : ℕ) : ℤ) - (a₀ : ℤ) := by
      have : ((g * n' : ℕ) : ℤ) - (a₀ : ℤ) = (g : ℤ) * ((n' : ℤ) - ((Nat.chineseRemainder hcop 0 n').val : ℤ)) := by
        simp [a₀]; ring
      rw [this, Nat.cast_mul]
      exact mul_dvd_mul_left (g : ℤ) hzd
    exact Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hzg)
  -- For any x ∈ range n, (d₁ ∣ x ∧ d₂ ∣ (n - x)) ↔ x % L = a₀ % L!
  have hiff : ∀ x < n, (d₁ ∣ x ∧ d₂ ∣ (n - x)) ↔ x % L = a₀ % L := by
    intro x hx
    constructor
    · intro ⟨h1, h2⟩
      have hm1 : x ≡ a₀ [MOD d₁] := by
        rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd h1, Nat.mod_eq_zero_of_dvd ha₀_d₁]
      have hm2 : x ≡ a₀ [MOD d₂] := by
        have hxn : x ≡ n [MOD d₂] := by
          have : x + (n - x) = n := by omega
          have h0 : x + (n - x) ≡ x + 0 [MOD d₂] :=
            Nat.ModEq.add_left x (Nat.modEq_zero_iff_dvd.mpr h2)
          simpa [this] using h0.symm
        exact hxn.trans ha₀_d₂.symm
      have hzd1 : (d₁ : ℤ) ∣ (x : ℤ) - (a₀ : ℤ) :=
        Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hm1.symm)
      have hzd2 : (d₂ : ℤ) ∣ (x : ℤ) - (a₀ : ℤ) :=
        Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hm2.symm)
      have hzl : (L : ℤ) ∣ (x : ℤ) - (a₀ : ℤ) := by
        have hnat : L ∣ Int.natAbs ((x : ℤ) - (a₀ : ℤ)) :=
          Nat.lcm_dvd (Int.natCast_dvd.mp hzd1) (Int.natCast_dvd.mp hzd2)
        exact Int.natCast_dvd.mpr hnat
      exact (Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hzl)).symm
    · intro hmod
      have hmL : x ≡ a₀ [MOD L] := hmod
      have hm1 : x ≡ a₀ [MOD d₁] := hmL.of_dvd (Nat.dvd_lcm_left d₁ d₂)
      have hm2 : x ≡ a₀ [MOD d₂] := hmL.of_dvd (Nat.dvd_lcm_right d₁ d₂)
      have h1 : d₁ ∣ x := by
        rw [← Nat.modEq_zero_iff_dvd]
        exact hm1.trans (Nat.modEq_zero_iff_dvd.mpr ha₀_d₁)
      have h2 : d₂ ∣ (n - x) := by
        have hxn : x ≡ n [MOD d₂] := hm2.trans ha₀_d₂
        have hsub : n - x + x = n := by omega
        have h0 : n - x + x ≡ 0 + x [MOD d₂] := by
          simpa [hsub] using hxn.symm
        exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' x h0)
      exact ⟨h1, h2⟩
  -- Compare crtPairCount n d₁ d₂ on Icc 2 (n-2) with range n (differs by at most 3 elements: 0, 1, n-1!)
  let S_full := (Finset.range n).filter (fun x => x % L = a₀ % L)
  let S_inner := (Finset.Icc 2 (n - 2)).filter (fun x => d₁ ∣ x ∧ d₂ ∣ (n - x))
  have hsub1 : S_inner ⊆ S_full := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hiff x (by omega)).mp hx.2⟩
  have hsub2 : S_full ⊆ S_inner ∪ {0, 1, n - 1} := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_union]
    by_cases hmid : 2 ≤ x ∧ x ≤ n - 2
    · left
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hmid, (hiff x hx.1).mpr hx.2⟩
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  have hc1 : S_inner.card ≤ S_full.card := Finset.card_le_card hsub1
  have hc2 : S_full.card ≤ S_inner.card + 3 := by
    calc S_full.card ≤ (S_inner ∪ {0, 1, n - 1}).card := Finset.card_le_card hsub2
      _ ≤ S_inner.card + ({0, 1, n - 1} : Finset ℕ).card := Finset.card_union_le _ _
      _ ≤ S_inner.card + 3 := by
          have : ({0, 1, n - 1} : Finset ℕ).card ≤ 3 := by
            calc ({0, 1, n - 1} : Finset ℕ).card ≤ ({1, n - 1} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
              _ ≤ ({n - 1} : Finset ℕ).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
              _ = 3 := by simp
          omega
  have hmod_b := card_mod_Ico_bounds (n := n) (L := L) (a := a₀) hL_pos
  have hL_rpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
  have hdiv_le : ((n / L : ℕ) : ℝ) ≤ (n : ℝ) / (L : ℝ) := by
    rw [le_div_iff₀ hL_rpos]
    exact_mod_cast Nat.div_mul_le_self n L
  have hlt_div : (n : ℝ) / (L : ℝ) < ((n / L : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hL_rpos]
    have : n < (n / L + 1) * L := by
      have := Nat.lt_div_mul_add hL_pos (a := n)
      linarith [mul_comm (n / L) L]
    exact_mod_cast this
  have hinner_eq : crtPairCount n d₁ d₂ = S_inner.card := rfl
  rw [hinner_eq, abs_le]
  have hc1_r : (S_inner.card : ℝ) ≤ (S_full.card : ℝ) := by exact_mod_cast hc1
  have hc2_r : (S_full.card : ℝ) ≤ (S_inner.card : ℝ) + 3 := by exact_mod_cast hc2
  have hb1_r : ((n / L : ℕ) : ℝ) ≤ (S_full.card : ℝ) := by exact_mod_cast hmod_b.1
  have hb2_r : (S_full.card : ℝ) ≤ ((n / L : ℕ) : ℝ) + 1 := by exact_mod_cast hmod_b.2
  constructor <;> linarith

/-! ### Part 3: Exact `ψ_n(h)` Factorization of the Region I CRT Weight -/

/-- Multiplicative singular-series weight on squarefree `h`:
`ψ_n(h) = ∏_{p | h} (if p ∣ n then p - 1 else -1)`. -/
def psiWeight (n h : ℕ) : ℤ :=
  ∏ p ∈ h.primeFactors, if p ∣ n then (p : ℤ) - 1 else -1

/-- Helper: a squarefree positive natural equals the product of its prime factors. -/
lemma prod_primeFactors_eq_self_of_squarefree {g : ℕ} (hg : Squarefree g) :
    ∏ p ∈ g.primeFactors, p = g := by
  have h1 : ∏ p ∈ g.primeFactors, p ^ g.factorization p = g := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hg.ne_zero
  conv_rhs => rw [← h1]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hge : 1 ≤ g.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hpp hg.ne_zero).mp (Nat.dvd_of_mem_primeFactors hp)
  have hle : g.factorization p ≤ 1 := by
    by_contra hgt; push Not at hgt
    have hp2 : p * p ∣ g := by
      simpa [sq] using (hpp.pow_dvd_iff_le_factorization hg.ne_zero).mpr hgt
    exact hpp.ne_one (Nat.isUnit_iff.mp (hg p hp2))
  rw [le_antisymm hle hge, pow_one]

/-- Helper: if every prime in a finset `s` of primes divides `n`, then `∏ p ∈ s, p ∣ n`. -/
lemma prod_primes_dvd_of_forall_dvd {s : Finset ℕ} {n : ℕ}
    (hs : ∀ p ∈ s, p.Prime) (hdvd : ∀ p ∈ s, p ∣ n) : (∏ p ∈ s, p) ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p t hpt ih =>
    rw [Finset.prod_insert hpt]
    have hp : p.Prime := hs p (Finset.mem_insert_self p t)
    have ht : ∀ q ∈ t, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ t, q) :=
      Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes hp (ht q hq)).mpr (fun h => hpt (h ▸ hq))
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd p (Finset.mem_insert_self p t))
      (ih ht (fun q hq => hdvd q (Finset.mem_insert_of_mem hq)))

/-- Helper: prime factors of a product of distinct primes equal the finset itself. -/
lemma primeFactors_prod_of_primes {t : Finset ℕ} (ht : ∀ q ∈ t, q.Prime) :
    (∏ q ∈ t, q).primeFactors = t := by
  classical
  have hpos : ∏ q ∈ t, q ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun q hq => (ht q hq).pos))
  ext p
  rw [Nat.mem_primeFactors]
  constructor
  · intro ⟨hp, hdvd, _⟩
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdvd
    exact ((Nat.prime_dvd_prime_iff_eq hp (ht q hq)).mp hpq) ▸ hq
  · intro hp
    exact ⟨ht p hp, Finset.dvd_prod_of_mem _ hp, hpos⟩

/-- **Theorem 3 (Exact Multiplicative Factorization of `1_{g | n} * g` for Squarefree `g`)**:
For every squarefree `g : ℕ`,
`(if g ∣ n then (g : ℤ) else 0) = ∑ h ∈ g.divisors, psiWeight n h`.
Dividing by `d₁ * d₂` yields the exact 1-variable singular-series factorization of Region I! -/
theorem gcd_dvd_indicator_eq_sum_psi (n : ℕ) {g : ℕ} (hg : Squarefree g) :
    (if g ∣ n then (g : ℤ) else 0) = ∑ h ∈ g.divisors, psiWeight n h := by
  classical
  have hg_pos : 0 < g := Nat.pos_of_ne_zero hg.ne_zero
  have hrad : ∏ p ∈ g.primeFactors, p = g := prod_primeFactors_eq_self_of_squarefree hg
  -- Step 1: LHS equals ∏_{p ∈ g.primeFactors} (1 + f p) where f p = if p ∣ n then p - 1 else -1
  let f : ℕ → ℤ := fun p => if p ∣ n then (p : ℤ) - 1 else -1
  have hlhs : (if g ∣ n then (g : ℤ) else 0) = ∏ p ∈ g.primeFactors, (1 + f p) := by
    by_cases hgn : g ∣ n
    · simp only [hgn, if_true]
      have hprod_p : ∏ p ∈ g.primeFactors, (1 + f p) = ∏ p ∈ g.primeFactors, (p : ℤ) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpn : p ∣ n := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hgn
        simp [f, hpn]
      rw [hprod_p, ← Nat.cast_prod, hrad]
    · simp only [hgn, if_false]
      have hex : ∃ p ∈ g.primeFactors, ¬(p ∣ n) := by
        by_contra hall
        push Not at hall
        have hdvd : (∏ p ∈ g.primeFactors, p) ∣ n :=
          prod_primes_dvd_of_forall_dvd (fun p hp => Nat.prime_of_mem_primeFactors hp) hall
        exact hgn (hrad ▸ hdvd)
      obtain ⟨p₀, hp₀, hp₀_nd⟩ := hex
      symm
      refine Finset.prod_eq_zero hp₀ ?_
      simp [f, hp₀_nd]
  -- Step 2: Expand ∏ (1 + f p) = ∑_{t ⊆ g.primeFactors} ∏_{p ∈ t} f p and biject with g.divisors
  rw [hlhs, Finset.prod_one_add]
  refine Finset.sum_bij (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Nat.mem_divisors]
    exact ⟨dvd_trans (Finset.prod_dvd_prod_of_subset t g.primeFactors id ht) (Nat.prod_primeFactors_dvd g),
      ne_of_gt hg_pos⟩
  · intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_powerset] at ht₁ ht₂
    have h1 := primeFactors_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors (ht₁ hq))
    have h2 := primeFactors_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors (ht₂ hq))
    rw [← h1, ← h2, heq]
  · intro h hh
    rw [Nat.mem_divisors] at hh
    have hsf_h : Squarefree h := hg.squarefree_of_dvd hh.1
    exact ⟨h.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hh.1 hh.2),
      prod_primeFactors_eq_self_of_squarefree hsf_h⟩
  · intro t ht
    rw [Finset.mem_powerset] at ht
    unfold psiWeight
    rw [primeFactors_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors (ht hq))]

/-! ### Part 4: Exact Bombieri–Vinogradov Exponent Bound for Region II -/

/-- **Theorem 4 (Exact Region II Bombieri–Vinogradov Exponent Inequality)**:
For every quadruple `d₁ * k₁ + d₂ * k₂ = n` in Region II with `1 ≤ d₁ ≤ D`, `Y < d₁ * d₂`,
`0 < k₂`, `g = gcd k₂ d₁`, `h = gcd (n / g) (d₁ / g)`, and reduced modulus `q = d₁ / (g * h)`:
`q ^ 2 * (k₂ * h) * Y < D ^ 3 * n`.
In particular, whenever `D ^ 3 ≤ Y` (e.g. `D = ⌊n^0.30⌋`, `Y = ⌊n^0.95⌋`, where `D^3 / Y ≤ n^(-0.05)`),
the reduced progression modulus `q` satisfies `q ^ 2 < (D ^ 3 / Y) * (n / (k₂ * h))`, placing
EVERY arithmetic progression in Region II strictly inside unconditional Bombieri–Vinogradov! -/
theorem regionII_bv_modulus_bound {n Y D d₁ k₁ d₂ k₂ : ℕ}
    (hd₁_pos : 0 < d₁) (hd₁_le : d₁ ≤ D) (hk₂_pos : 0 < k₂)
    (heq : d₁ * k₁ + d₂ * k₂ = n) (hY : Y < d₁ * d₂) :
    let g := Nat.gcd k₂ d₁
    let h := Nat.gcd (n / g) (d₁ / g)
    let q := d₁ / (g * h)
    q ^ 2 * (k₂ * h) * Y < D ^ 3 * n := by
  intro g h q
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right k₂ hd₁_pos
  have hg_dvd_d₁ : g ∣ d₁ := Nat.gcd_dvd_right k₂ d₁
  have hd₁g_pos : 0 < d₁ / g := Nat.div_pos (Nat.le_of_dvd hd₁_pos hg_dvd_d₁) hg_pos
  have hh_pos : 0 < h := Nat.gcd_pos_of_pos_right (n / g) hd₁g_pos
  have hh_dvd : h ∣ d₁ / g := Nat.gcd_dvd_right (n / g) (d₁ / g)
  have hgh_dvd : g * h ∣ d₁ := by
    have : g * h ∣ g * (d₁ / g) := Nat.mul_dvd_mul_left g hh_dvd
    rwa [Nat.mul_div_cancel' hg_dvd_d₁] at this
  have hq_mul : q * (g * h) = d₁ := Nat.div_mul_cancel hgh_dvd
  -- Step 1: q^2 * h ≤ d₁^2 (since q * g * h = d₁ and g ≥ 1, h ≥ 1)
  have hq2h_le : q ^ 2 * h ≤ d₁ ^ 2 := by
    have h1 : q ^ 2 * h ≤ q ^ 2 * (g ^ 2 * h ^ 2) := by
      have : h ≤ g ^ 2 * h ^ 2 := by
        have hg1 : 1 ≤ g ^ 2 := Nat.one_le_pow 2 g hg_pos
        have hh2 : h ≤ h ^ 2 := by nlinarith
        nlinarith
      exact Nat.mul_le_mul_left (q ^ 2) this
    have h2 : q ^ 2 * (g ^ 2 * h ^ 2) = (q * (g * h)) ^ 2 := by ring
    rw [h2, hq_mul] at h1
    exact h1
  -- Step 2: k₂ * Y < d₁ * n (since d₂ * k₂ ≤ n and Y < d₁ * d₂)
  have hk₂Y_lt : k₂ * Y < d₁ * n := by
    have h1 : k₂ * Y < k₂ * (d₁ * d₂) := Nat.mul_lt_mul_of_pos_left hY hk₂_pos
    have h2 : d₂ * k₂ ≤ n := by omega
    have h3 : k₂ * (d₁ * d₂) = d₁ * (d₂ * k₂) := by ring
    have h4 : d₁ * (d₂ * k₂) ≤ d₁ * n := Nat.mul_le_mul_left d₁ h2
    omega
  -- Combine Step 1 and Step 2:
  have hd₁_cube : d₁ ^ 3 ≤ D ^ 3 := Nat.pow_le_pow_left hd₁_le 3
  calc q ^ 2 * (k₂ * h) * Y
      = (q ^ 2 * h) * (k₂ * Y) := by ring
    _ ≤ d₁ ^ 2 * (k₂ * Y) := Nat.mul_le_mul_right (k₂ * Y) hq2h_le
    _ < d₁ ^ 2 * (d₁ * n) := Nat.mul_lt_mul_of_pos_left hk₂Y_lt (Nat.pow_pos hd₁_pos)
    _ = d₁ ^ 3 * n := by ring
    _ ≤ D ^ 3 * n := Nat.mul_le_mul_right n hd₁_cube

end GoldbachWave10
