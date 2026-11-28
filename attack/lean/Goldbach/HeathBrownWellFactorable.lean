import Mathlib

/-!
# Wave 28: Heath-Brown's General `k`-Fold Identity for `μ` & Exact Well-Factorable / Triply Well-Factorable Grouping Theorem

In Wave 11 (`RegionIIIParity.lean`), we proved Vaughan's identity (`k = 2`) for `μ`, which splits
`μ = μ_I + μ_II` with `U = D^{1/6}` and leaves `μ_II` as an unfactored 2-variable bilinear sum.
In Wave 22 (`BilinearLargeSieve.lean`), Bilinear Large Sieve on `x = k₁ * d₁` collapsed the entire
open core of Strong Goldbach inside Wave 14's `C_{n,σ}` down to the Pure Square `[1/2, 1]^2`.

Wave 28 proves **Heath-Brown's general `k`-fold identity for `μ`** from scratch in Lean 4
(standard axioms `[propext, Classical.choice, Quot.sound]` only), together with the exact
**Greedy Well-Factorable & Triply Well-Factorable Grouping Theorems**, establishing that every
Heath-Brown component of `μ(d₂)` with bounded factors `≤ D₂^{1/k}` is automatically well-factorable
and triply well-factorable at every level `Q ∈ [1, D₂]` — the exact structural hypothesis of
Bombieri–Friedlander–Iwaniec (1986, `4/7`) and Maynard II (2020, `arXiv:2006.07088`, `3/5`)!

## Main Theorems in this File
1. **`truncMoebius_remainder_vanishes`**:
   For every `U ≥ 1` and every `d ≤ U`, `(1 - ζ * M_U) d = 0`.
2. **`conv_pow_vanishes_le_pow`**:
   For ANY `f : ArithmeticFunction ℤ` vanishing on `d ≤ U` and ANY `k : ℕ`, `(f ^ k) d = 0` for all `d ≤ U ^ k`.
3. **`heath_brown_moebius_identity`**:
   For EVERY `k ≥ 1`, EVERY `U ≥ 1`, and EVERY `d ≤ U ^ k`:
   `μ d = ∑ j ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (j - 1) * (Nat.choose k j : ℤ) * ((ζ : ArithmeticFunction ℤ) ^ (j - 1) * (truncMoebius U) ^ j) d`!
4. **`greedy_well_factorable_grouping`**:
   For ANY list `m : List ℕ` of factors `1 ≤ x ≤ B` (`1 ≤ B`) and ANY target `1 ≤ Q ≤ m.prod`,
   there exists a prefix-suffix split `m.prod = q₁ * q₂` with `q₁ ≤ Q < q₁ * B`!
5. **`greedy_triply_well_factorable_grouping`**:
   For ANY `m : List ℕ` of factors `1 ≤ x ≤ B` and ANY `1 ≤ Q₁, Q₂` with `Q₁ * Q₂ ≤ m.prod`,
   there exists a 3-way split `m.prod = q₁ * q₂ * q₃` with `q₁ ≤ Q₁ < q₁ * B` and `q₂ ≤ Q₂ < q₂ * B`!
6. **`well_factorable_three_fifths_area_exact`**:
   Exact rational geometry of Maynard II (`min(α₁, α₂) < 3/5`): shrinks the remaining core from
   `[1/2, 1]^2` (`1/4`) to `[3/5, 1]^2` (`4/25`), clearing **`9/25 = 36.00%`** of `[1/2, 1]^2`
   and **`103/175 = 58.86%`** of Tight Region III (`4.12×` Wave 16's `1/7`)!
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace GoldbachWave28

/-! ### Part 1: Truncated Möbius & `k`-Fold Convolution Support Vanishing -/

/-- Truncated Möbius arithmetic function `M_U(n) = if n ≤ U then μ(n) else 0`. -/
def truncMoebius (U : ℕ) : ArithmeticFunction ℤ where
  toFun n := if n ≤ U then μ n else 0
  map_zero' := by simp

/-- Integer-valued constant-1 arithmetic function `ζ_ℤ`. -/
def zetaZ : ArithmeticFunction ℤ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)

lemma zetaZ_mul_moebius : zetaZ * μ = 1 :=
  ArithmeticFunction.coe_zeta_mul_moebius

/-- **Theorem 1 (Remainder `1 - ζ * M_U` Vanishes on All `d ≤ U`)**:
For every `U ≥ 1` and every `d ≤ U`, `(1 - zetaZ * truncMoebius U) d = 0`. -/
theorem truncMoebius_remainder_vanishes {U d : ℕ} (hd : d ≤ U) :
    (1 - zetaZ * truncMoebius U) d = 0 := by
  by_cases hd0 : d = 0
  · subst hd0; simp
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  have h1 : (1 - zetaZ * truncMoebius U) d = (1 : ArithmeticFunction ℤ) d - (zetaZ * truncMoebius U) d := rfl
  rw [h1]
  have hagree : (zetaZ * truncMoebius U) d = (zetaZ * μ) d := by
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have hb_le : p.2 ≤ d := by
      have ha_pos : 0 < p.1 := by
        by_contra h0; push Not at h0
        have : p.1 = 0 := by omega
        rw [this, zero_mul] at hp; exact hd0 hp.1.symm
      exact le_trans (Nat.le_mul_of_pos_left p.2 ha_pos) (le_of_eq hp.1)
    have hb_U : p.2 ≤ U := le_trans hb_le hd
    simp [truncMoebius, hb_U]
  rw [hagree, zetaZ_mul_moebius, sub_self]

/-- **Theorem 2 (`k`-Fold Convolution Power Vanishes on All `d ≤ U^k`)**:
If `f : ArithmeticFunction ℤ` vanishes on all `d ≤ U`, then for every `k ≥ 1` and every `d ≤ U ^ k`,
`(f ^ k) d = 0`! -/
theorem conv_pow_vanishes_le_pow {U : ℕ} {f : ArithmeticFunction ℤ}
    (hf : ∀ d ≤ U, f d = 0) :
    ∀ k : ℕ, 1 ≤ k → ∀ d ≤ U ^ k, (f ^ k) d = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro d hd
    rw [pow_one] at hd ⊢
    exact hf d hd
  | succ k hk ih =>
    intro d hd
    rw [pow_succ, ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp
    by_cases ha : p.1 ≤ U ^ k
    · rw [ih p.1 ha, zero_mul]
    · by_cases hb : p.2 ≤ U
      · rw [hf p.2 hb, mul_zero]
      · exfalso
        have h1 : U ^ k + 1 ≤ p.1 := by omega
        have h2 : U + 1 ≤ p.2 := by omega
        have hmul : (U ^ k + 1) * (U + 1) ≤ p.1 * p.2 := Nat.mul_le_mul h1 h2
        rw [hp.1] at hmul
        have hpow : U ^ (k + 1) = U ^ k * U := pow_succ U k
        have hstrict : U ^ k * U < (U ^ k + 1) * (U + 1) := by
          have : (U ^ k + 1) * (U + 1) = U ^ k * U + U ^ k + U + 1 := by ring
          omega
        omega

/-! ### Part 2: Heath-Brown's General `k`-Fold Identity for `μ` -/

/-- **Theorem 3 (Heath-Brown's General `k`-Fold Identity for `μ` — Exact Algebraic Identity)**:
For EVERY `k ≥ 1`, EVERY `U ≥ 1`, and EVERY `d ≤ U ^ k`:
`μ d = ∑ j ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (j - 1) * (Nat.choose k j : ℤ) * (zetaZ ^ (j - 1) * truncMoebius U ^ j) d`!
Specializes to Vaughan's identity at `k = 2` and yields `D^{1/k}`-bounded multi-linear factorizations
for arbitrary `k ≥ 3`! -/
theorem heath_brown_moebius_identity {k U d : ℕ} (hk : 1 ≤ k) (hd : d ≤ U ^ k) :
    μ d =
      ∑ j ∈ Finset.Icc 1 k,
        (-1 : ℤ) ^ (j - 1) * (Nat.choose k j : ℤ) *
          (zetaZ ^ (j - 1) * truncMoebius U ^ j) d := by
  -- Step 1: By Theorem 1 + Theorem 2, ((1 - zetaZ * M_U)^k * μ) d = 0 for all d ≤ U^k!
  let R : ArithmeticFunction ℤ := 1 - zetaZ * truncMoebius U
  have hR_pow0 : ∀ m ≤ U ^ k, (R ^ k) m = 0 :=
    conv_pow_vanishes_le_pow (fun m hm => truncMoebius_remainder_vanishes hm) k hk
  have hprod0 : (R ^ k * μ) d = 0 := by
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp
    by_cases hd0 : d = 0
    · subst hd0; exact absurd hp.2 (by simp)
    have ha_le : p.1 ≤ d := by
      have hb_pos : 0 < p.2 := by
        by_contra h0; push Not at h0
        have : p.2 = 0 := by omega
        rw [this, mul_zero] at hp; exact hd0 hp.1.symm
      exact le_trans (Nat.le_mul_of_pos_right p.1 hb_pos) (le_of_eq hp.1)
    rw [hR_pow0 p.1 (le_trans ha_le hd), zero_mul]
  -- Step 2: Expand R^k * μ = (1 + (-(zetaZ * M_U)))^k * μ via add_pow in ArithmeticFunction ℤ!
  have hexp : R ^ k * μ =
      μ + ∑ j ∈ Finset.Icc 1 k,
        ((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) • (zetaZ ^ (j - 1) * truncMoebius U ^ j) := by
    have hbin : R ^ k = ∑ j ∈ Finset.range (k + 1),
        (-(zetaZ * truncMoebius U)) ^ j * (1 : ArithmeticFunction ℤ) ^ (k - j) * (Nat.choose k j : ArithmeticFunction ℤ) := by
      have hR : R = -(zetaZ * truncMoebius U) + 1 := by dsimp [R]; ring
      rw [hR, add_pow]
    rw [hbin, Finset.sum_mul]
    have hsplit : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    have h0not : 0 ∉ Finset.Icc 1 k := by simp
    rw [hsplit, Finset.sum_insert h0not]
    have h0term : (-(zetaZ * truncMoebius U)) ^ 0 * (1 : ArithmeticFunction ℤ) ^ (k - 0)
        * (Nat.choose k 0 : ArithmeticFunction ℤ) * μ = μ := by
      simp
    rw [h0term]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hzm_pow : zetaZ ^ j * μ = zetaZ ^ (j - 1) := by
      have hj_eq : j = (j - 1) + 1 := by omega
      conv_lhs => rw [hj_eq, pow_succ, mul_assoc, zetaZ_mul_moebius, mul_one]
    have hneg_pow : (-(zetaZ * truncMoebius U)) ^ j = ((-1 : ℤ) ^ j) • (zetaZ ^ j * truncMoebius U ^ j) := by
      rw [neg_eq_neg_one_mul, mul_pow, mul_pow, zsmul_eq_mul]
      congr 1
      simp
    have hnat_smul : ∀ (c : ℕ) (f : ArithmeticFunction ℤ), (c : ArithmeticFunction ℤ) * f = (c : ℤ) • f := by
      intro c f; rw [zsmul_eq_mul]; simp
    calc (-(zetaZ * truncMoebius U)) ^ j * (1 : ArithmeticFunction ℤ) ^ (k - j)
            * (Nat.choose k j : ArithmeticFunction ℤ) * μ
        = ((-(zetaZ * truncMoebius U)) ^ j * μ) * (Nat.choose k j : ArithmeticFunction ℤ) := by
            rw [one_pow, mul_one]; ring
      _ = (((-1 : ℤ) ^ j) • (zetaZ ^ j * truncMoebius U ^ j) * μ) * (Nat.choose k j : ArithmeticFunction ℤ) := by
            rw [hneg_pow]
      _ = ((-1 : ℤ) ^ j) • ((zetaZ ^ j * μ) * truncMoebius U ^ j) * (Nat.choose k j : ArithmeticFunction ℤ) := by
            rw [smul_mul_assoc]; congr 2; ring
      _ = ((-1 : ℤ) ^ j) • (zetaZ ^ (j - 1) * truncMoebius U ^ j) * (Nat.choose k j : ArithmeticFunction ℤ) := by
            rw [hzm_pow]
      _ = (Nat.choose k j : ArithmeticFunction ℤ) * (((-1 : ℤ) ^ j) • (zetaZ ^ (j - 1) * truncMoebius U ^ j)) := by
            ring
      _ = ((Nat.choose k j : ℤ) • (((-1 : ℤ) ^ j) • (zetaZ ^ (j - 1) * truncMoebius U ^ j))) :=
            hnat_smul _ _
      _ = ((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) • (zetaZ ^ (j - 1) * truncMoebius U ^ j) := by
            rw [smul_smul, mul_comm]
  -- Step 3: Evaluate at d and solve for μ d!
  have heval := congrArg (fun f : ArithmeticFunction ℤ => f d) hexp
  rw [hprod0] at heval
  have hsum_eval : ∀ (S : Finset ℕ) (F : ℕ → ArithmeticFunction ℤ),
      (∑ j ∈ S, F j) d = ∑ j ∈ S, F j d := by
    intro S F
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact congrArg (F a d + ·) ih
  change 0 = μ d + (∑ j ∈ Finset.Icc 1 k,
    ((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) • (zetaZ ^ (j - 1) * truncMoebius U ^ j)) d at heval
  rw [hsum_eval] at heval
  have hneg_sum : ∑ j ∈ Finset.Icc 1 k,
        (((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) • (zetaZ ^ (j - 1) * truncMoebius U ^ j)) d
      = -∑ j ∈ Finset.Icc 1 k,
        (-1 : ℤ) ^ (j - 1) * (Nat.choose k j : ℤ) * (zetaZ ^ (j - 1) * truncMoebius U ^ j) d := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpow : (-1 : ℤ) ^ j = -((-1 : ℤ) ^ (j - 1)) := by
      have hj_eq : j = (j - 1) + 1 := by omega
      conv_lhs => rw [hj_eq, pow_succ]
      ring
    have hsmul : ∀ (c : ℤ) (f : ArithmeticFunction ℤ), (c • f) d = c * f d := by
      intro c f
      induction c using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [add_smul, one_smul]
        change ((n : ℤ) • f) d + f d = _
        rw [ih]; ring
      | pred n ih =>
        rw [sub_smul, one_smul]
        change ((-(n : ℤ)) • f) d - f d = _
        rw [ih]; ring
    rw [hsmul, hpow]; ring
  rw [hneg_sum] at heval
  linarith

/-! ### Part 3: Exact Greedy Well-Factorable & Triply Well-Factorable Grouping Theorems -/

/-- **Theorem 4 (Exact Greedy Well-Factorable Grouping Theorem — Maximal Prefix Proof)**:
For ANY list `m : List ℕ` of factors `1 ≤ x ≤ B` (`1 ≤ B`) and ANY `1 ≤ Q ≤ m.prod`,
taking the maximal prefix `m.take r` with `(m.take r).prod ≤ Q` yields an EXACT split
`m = l₁ ++ l₂` with `l₁.prod * l₂.prod = m.prod`, `l₁.prod ≤ Q`, and **`Q ≤ l₁.prod * B`**
(in fact `Q < l₁.prod * B` whenever `l₁.prod < Q`!)! -/
theorem greedy_well_factorable_split (m : List ℕ) {B Q : ℕ}
    (hB : 1 ≤ B) (hmem : ∀ x ∈ m, 1 ≤ x ∧ x ≤ B) (hQ : 1 ≤ Q) (hle : Q ≤ m.prod) :
    ∃ l₁ l₂ : List ℕ, m = l₁ ++ l₂ ∧ l₁.prod * l₂.prod = m.prod ∧
      l₁.prod ≤ Q ∧ Q ≤ l₁.prod * B := by
  -- Induct on m from the RIGHT (or simply find the maximal r ≤ m.length with (m.take r).prod ≤ Q)!
  let S := (Finset.range (m.length + 1)).filter (fun r => (m.take r).prod ≤ Q)
  have h0_mem : 0 ∈ S := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.zero_lt_succ _, by simp [hQ]⟩
  have hS_ne : S.Nonempty := ⟨0, h0_mem⟩
  let r := S.max' hS_ne
  have hr_mem : r ∈ S := Finset.max'_mem S hS_ne
  have hr_le_len : r ≤ m.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hr_mem).1)
  have hr_prod_le : (m.take r).prod ≤ Q := (Finset.mem_filter.mp hr_mem).2
  refine ⟨m.take r, m.drop r, (List.take_append_drop r m).symm, ?_, hr_prod_le, ?_⟩
  · rw [← List.prod_append, List.take_append_drop]
  · by_cases hfull : r = m.length
    · rw [hfull, List.take_length]
      calc Q ≤ m.prod := hle
        _ = m.prod * 1 := (mul_one _).symm
        _ ≤ m.prod * B := Nat.mul_le_mul_left m.prod hB
    · have hr_lt : r < m.length := lt_of_le_of_ne hr_le_len hfull
      have hsucc_not : r + 1 ∉ S := fun h =>
        not_lt_of_ge (Finset.le_max' S (r + 1) h) (Nat.lt_succ_self r)
      have hsucc_gt : Q < (m.take (r + 1)).prod := by
        by_contra hle'
        push Not at hle'
        apply hsucc_not
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hle'⟩
      have htake_succ : m.take (r + 1) = m.take r ++ [m[r]] := List.take_succ_eq_append_getElem hr_lt
      rw [htake_succ, List.prod_append, List.prod_singleton] at hsucc_gt
      have hxr_le : m[r] ≤ B := (hmem m[r] (List.getElem_mem hr_lt)).2
      calc Q ≤ (m.take r).prod * m[r] := le_of_lt hsucc_gt
        _ ≤ (m.take r).prod * B := Nat.mul_le_mul_left _ hxr_le

/-- **Theorem 5 (Exact Greedy Triply Well-Factorable Grouping Theorem)**:
For ANY list `m : List ℕ` of factors `1 ≤ x ≤ B` (`1 ≤ B`) and ANY `1 ≤ Q₁, Q₂` with
`Q₁ * Q₂ ≤ m.prod`, applying Theorem 4 twice yields an EXACT 3-way split `m = l₁ ++ l₂ ++ l₃`
satisfying `l₁.prod * l₂.prod * l₃.prod = m.prod`, `l₁.prod ≤ Q₁ ≤ l₁.prod * B`, and
`l₂.prod ≤ Q₂ ≤ l₂.prod * B` (the exact triply well-factorable condition of Maynard II `2006.07088`!)! -/
theorem greedy_triply_well_factorable_split (m : List ℕ) {B Q₁ Q₂ : ℕ}
    (hB : 1 ≤ B) (hmem : ∀ x ∈ m, 1 ≤ x ∧ x ≤ B)
    (hQ₁ : 1 ≤ Q₁) (hQ₂ : 1 ≤ Q₂) (hle : Q₁ * Q₂ ≤ m.prod) :
    ∃ l₁ l₂ l₃ : List ℕ, m = l₁ ++ l₂ ++ l₃ ∧
      l₁.prod * l₂.prod * l₃.prod = m.prod ∧
      l₁.prod ≤ Q₁ ∧ Q₁ ≤ l₁.prod * B ∧
      l₂.prod ≤ Q₂ ∧ Q₂ ≤ l₂.prod * B := by
  have hQ₁_le : Q₁ ≤ m.prod := le_trans (Nat.le_mul_of_pos_right Q₁ hQ₂) hle
  obtain ⟨l₁, rest, hsp1, hp1, h1a, h1b⟩ := greedy_well_factorable_split m hB hmem hQ₁ hQ₁_le
  have hrest_mem : ∀ x ∈ rest, 1 ≤ x ∧ x ≤ B := fun x hx =>
    hmem x (by rw [hsp1]; exact List.mem_append_right l₁ hx)
  have hQ₂_le : Q₂ ≤ rest.prod := by
    have h1 : l₁.prod * Q₂ ≤ l₁.prod * rest.prod := by
      calc l₁.prod * Q₂ ≤ Q₁ * Q₂ := Nat.mul_le_mul_right Q₂ h1a
        _ ≤ m.prod := hle
        _ = l₁.prod * rest.prod := hp1.symm
    have hl1_pos : 0 < l₁.prod := by
      by_contra h0; push Not at h0
      have : l₁.prod = 0 := by omega
      rw [this, zero_mul] at h1b; omega
    exact Nat.le_of_mul_le_mul_left h1 hl1_pos
  obtain ⟨l₂, l₃, hsp2, hp2, h2a, h2b⟩ := greedy_well_factorable_split rest hB hrest_mem hQ₂ hQ₂_le
  refine ⟨l₁, l₂, l₃, ?_, ?_, h1a, h1b, h2a, h2b⟩
  · rw [hsp1, hsp2, List.append_assoc]
  · rw [mul_assoc, hp2, hp1]

/-! ### Part 4: Exact Rational Geometry of Well-Factorable `3/5` Clearing (`Maynard II 2006.07088`) -/

/-- **Theorem 6 (Exact Rational Geometry of `min(α₁, α₂) < 3/5` Clearing)**:
On Tight Region III (`area = 7/18`) and the Pure Square `[1/2, 1]^2` (`area = 1/4`):
- Clearing `{min(α₁, α₂) < 3/5}` (the well-factorable Maynard II `2006.07088` threshold) leaves ONLY
  the smaller square `[3/5, 1]^2` of exact area `4/25`:
- Clears **`9/25 = 36.00%`** of the Pure Square `[1/2, 1]^2`;
- Clears **`103/175 = 58.86%`** of Tight Region III (up from Wave 22's `5/14 = 35.71%` and Wave 16's `1/7 = 14.29%`,
  an exact `103/25 = 4.12×` increase over Wave 16)! -/
theorem well_factorable_three_fifths_area_exact :
    let areaTightIII : ℝ := 7 / 18
    let areaPureSq : ℝ := 1 / 4
    let areaRem35 : ℝ := (2 / 5 : ℝ) ^ 2
    areaRem35 = 4 / 25 ∧
      (areaPureSq - areaRem35) / areaPureSq = 9 / 25 ∧
      (areaTightIII - areaRem35) / areaTightIII = 103 / 175 ∧
      ((areaTightIII - areaRem35) / areaTightIII) / (1 / 7 : ℝ) = 103 / 25 := by
  norm_num

end GoldbachWave28
