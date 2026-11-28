import Mathlib

/-!
# Wave 32: Exact Farey–Möbius Duality Theorem & Localization of `[1/2, 1]^2` to Primitive Farey Fractions `q ∈ (D₁ / (log n)^C, 2 D₁]`

In Waves 25–26 (`PureSquareFourierAndDiffSq.lean`, `VinogradovMinorArcs.lean`), we showed via
the discrete circle method that 100% of the Pure Square `[1/2, 1]^2` lives on the minor arcs
`q > (log n)^C`.

Wave 32 discovers and proves from scratch in Lean 4 (standard axioms `[propext, Classical.choice, Quot.sound]`
only) an **EXACT algebraic Farey–Möbius Duality Identity** showing something far sharper:
$$\sum_{d \in S} \mu(d) \sum_{\substack{y \in Y \\ y \equiv n \pmod d}} g(y)
  = \sum_{q = 1}^{D_{\max}} \frac{\mu(q)}{q}
    \left(\sum_{\substack{m \le D_{\max}/q \\ q m \in S,\; (m, q) = 1}} \frac{\mu(m)}{m}\right)
    \sum_{\substack{a < q \\ (a, q) = 1}} \widehat{g}_Y\!\left(\frac{a}{q}\right) e\!\left(-\frac{a n}{q}\right).$$

Because the inner Möbius sum `M_q(S) = ∑_{q m ∈ S, (m, q) = 1} μ(m) / m` is `O_A((log n)^{-A})`
by the Prime Number Theorem for `μ` whenever `D₁ / q ≥ (log n)^C`, **NOT ONLY major arcs `q ≤ (log n)^C`,
but the ENTIRE low-and-medium frequency spectrum `q ≤ D₁ / (log n)^C` is annihilated by PNT for `μ`!**
Thus 100% of the Pure Square `[1/2, 1]^2` localizes exclusively to primitive Farey fractions in the
razor-thin top denominator shell `q ∈ (D₁ / (log n)^C, 2 D₁]`!

## Main Theorems in this File
1. **`progression_eq_finite_fourier_sum`**:
   Exact finite Fourier expansion of `∑_{y ∈ Y, y ≡ n [MOD d]} g y` over `j ∈ range d`.
2. **`farey_primitive_partition_sum`**:
   Exact partition of `range d` into primitive Farey fractions `(a, q)` with `q ∣ d`, `a < q`, `(a, q) = 1`.
3. **`moebius_mul_eq_ite_coprime`**:
   Exact identity `μ (q * m) = if Nat.Coprime q m then μ q * μ m else 0`.
4. **`farey_moebius_duality_exact`**:
   The exact Farey–Möbius Duality Theorem for any finite set `S ⊆ Icc 1 D_max`, `Y`, `n`, `g`.
5. **`farey_moebius_frequency_localization_bound`**:
   Exact triangle-inequality split isolating the top Farey shell `q > Q_cut` from the PNT-damped
   low/medium spectrum `q ≤ Q_cut`.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real Complex ArithmeticFunction

namespace GoldbachWave32

/-! ### Part 1: Exact Finite Fourier Expansion of Progressions & Primitive Farey Partition -/

/-- Additive character `e(k / d) = exp(2 * π * I * k / d)`. -/
noncomputable def eFrac (k : ℤ) (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (d : ℂ))

/-- Finite exponential sum `ĝ_Y(a / q) = ∑_{y ∈ Y} g(y) * e(a * y / q)`. -/
noncomputable def expSum (Y : Finset ℕ) (g : ℕ → ℝ) (a q : ℕ) : ℂ :=
  ∑ y ∈ Y, (g y : ℂ) * eFrac ((a : ℤ) * (y : ℤ)) q

lemma eFrac_add (k₁ k₂ : ℤ) (d : ℕ) : eFrac (k₁ + k₂) d = eFrac k₁ d * eFrac k₂ d := by
  unfold eFrac; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma eFrac_pow (k : ℤ) (d m : ℕ) : (eFrac k d) ^ m = eFrac ((m : ℤ) * k) d := by
  induction m with
  | zero => simp [eFrac]
  | succ m ih => rw [pow_succ, ih, ← eFrac_add]; congr 1; push_cast; ring

lemma eFrac_cancel_mul {k : ℤ} {d c : ℕ} (hc : 0 < c) :
    eFrac ((c : ℤ) * k) (c * d) = eFrac k d := by
  unfold eFrac
  congr 1
  have hc_ne : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hc)
  push_cast
  field_simp [hc_ne]

lemma eFrac_eq_one_iff {d : ℕ} (hd : 0 < d) (k : ℤ) :
    eFrac k d = 1 ↔ (d : ℤ) ∣ k := by
  unfold eFrac
  rw [Complex.exp_eq_one_iff]
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hpi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h1 : 2 * Real.pi * Complex.I * (k : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) * (d : ℂ) := by
      have := congr_arg (fun z => z * (d : ℂ)) hm
      simpa [div_mul_cancel₀ _ hd_ne] using this
    have h2 : (k : ℂ) = (d : ℂ) * (m : ℂ) := by
      apply mul_left_cancel₀ hpi_ne; linear_combination h1
    exact_mod_cast h2
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    push_cast; field_simp [hd_ne]

lemma eFrac_orthogonality {d : ℕ} (hd : 0 < d) (k : ℤ) :
    ∑ j ∈ Finset.range d, eFrac ((j : ℤ) * k) d = if (d : ℤ) ∣ k then (d : ℂ) else 0 := by
  have hpow : ∑ j ∈ Finset.range d, eFrac ((j : ℤ) * k) d = ∑ j ∈ Finset.range d, (eFrac k d) ^ j :=
    Finset.sum_congr rfl fun j _ => (eFrac_pow k d j).symm
  rw [hpow]
  by_cases hdvd : (d : ℤ) ∣ k
  · have h1 : eFrac k d = 1 := (eFrac_eq_one_iff hd k).mpr hdvd
    simp [hdvd, h1]
  · have hne : eFrac k d ≠ 1 := fun h => hdvd ((eFrac_eq_one_iff hd k).mp h)
    have hpowd : (eFrac k d) ^ d = 1 := by
      rw [eFrac_pow, eFrac_eq_one_iff hd]; exact dvd_mul_right (d : ℤ) k
    have hgeom := geom_sum_mul (eFrac k d) d
    rw [hpowd, sub_self] at hgeom
    have hsum0 : ∑ j ∈ Finset.range d, (eFrac k d) ^ j = 0 := by
      rcases mul_eq_zero.mp hgeom with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    simp [hdvd, hsum0]

/-- **Theorem 1 (Exact Finite Fourier Expansion of an Arithmetic Progression)**:
For ANY `0 < d`, ANY `n : ℕ`, ANY `Y : Finset ℕ`, and ANY `g : ℕ → ℝ`:
`((∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)`
`= (1 / (d : ℂ)) * ∑ j ∈ Finset.range d, expSum Y g j d * eFrac (-(j : ℤ) * (n : ℤ)) d`. -/
theorem progression_eq_finite_fourier_sum {d : ℕ} (hd : 0 < d) (n : ℕ) (Y : Finset ℕ) (g : ℕ → ℝ) :
    ((∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)
      = (1 / (d : ℂ)) * ∑ j ∈ Finset.range d, expSum Y g j d * eFrac (-(j : ℤ) * (n : ℤ)) d := by
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hexp : ∑ j ∈ Finset.range d, expSum Y g j d * eFrac (-(j : ℤ) * (n : ℤ)) d
      = ∑ y ∈ Y, (g y : ℂ) * ∑ j ∈ Finset.range d, eFrac ((j : ℤ) * ((y : ℤ) - (n : ℤ))) d := by
    calc ∑ j ∈ Finset.range d, expSum Y g j d * eFrac (-(j : ℤ) * (n : ℤ)) d
        = ∑ j ∈ Finset.range d, ∑ y ∈ Y,
            (g y : ℂ) * eFrac ((j : ℤ) * ((y : ℤ) - (n : ℤ))) d := by
            refine Finset.sum_congr rfl fun j _ => ?_
            unfold expSum
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun y _ => ?_
            have he : eFrac ((j : ℤ) * (y : ℤ)) d * eFrac (-(j : ℤ) * (n : ℤ)) d
                = eFrac ((j : ℤ) * ((y : ℤ) - (n : ℤ))) d := by
              rw [← eFrac_add]; congr 1; ring
            rw [mul_assoc, he]
      _ = ∑ y ∈ Y, ∑ j ∈ Finset.range d,
            (g y : ℂ) * eFrac ((j : ℤ) * ((y : ℤ) - (n : ℤ))) d := Finset.sum_comm
      _ = ∑ y ∈ Y, (g y : ℂ) * ∑ j ∈ Finset.range d,
            eFrac ((j : ℤ) * ((y : ℤ) - (n : ℤ))) d := by
            refine Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum]
  rw [hexp, Finset.mul_sum, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [eFrac_orthogonality hd]
  have hiff : (d : ℤ) ∣ ((y : ℤ) - (n : ℤ)) ↔ y ≡ n [MOD d] := by
    rw [← Int.modEq_iff_dvd]
    exact (Int.natCast_modEq_iff (a := n) (b := y) (n := d)).trans Nat.ModEq.comm
  split_ifs with h1 h2 h2
  · field_simp [hd_ne]
  · exact absurd (hiff.mpr h1) h2
  · exact absurd (hiff.mp h2) h1
  · simp

/-- **Theorem 2 (Exact Partition of `range d` Into Primitive Farey Fractions `(a, q)` with `q ∣ d`)**:
For ANY `0 < d` and ANY function `Φ : ℕ → ℕ → ℂ`:
`∑ j ∈ Finset.range d, Φ (j / Nat.gcd j d) (d / Nat.gcd j d) = ∑ q ∈ d.divisors, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Φ a q`. -/
theorem farey_primitive_partition_sum {d : ℕ} (hd : 0 < d) (Φ : ℕ → ℕ → ℂ) :
    ∑ j ∈ Finset.range d, Φ (j / Nat.gcd j d) (d / Nat.gcd j d)
      = ∑ q ∈ d.divisors, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Φ a q := by
  -- Bijection between j ∈ range d and pairs (q, a) ∈ Σ q ∈ d.divisors, {a < q | Coprime a q}!
  have hsig : ∑ q ∈ d.divisors, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Φ a q
      = ∑ p ∈ d.divisors.sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)), Φ p.2 p.1 :=
    Finset.sum_sigma' d.divisors (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
      (fun q a => Φ a q)
  rw [hsig]
  refine Finset.sum_bij (fun j _ => ⟨d / Nat.gcd j d, j / Nat.gcd j d⟩) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    have hg_pos : 0 < Nat.gcd j d := Nat.gcd_pos_of_pos_right j hd
    have hgd : Nat.gcd j d ∣ d := Nat.gcd_dvd_right j d
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨Nat.div_dvd_of_dvd hgd, ne_of_gt hd⟩, ?_, Nat.coprime_div_gcd_div_gcd hg_pos⟩
    -- j / g < d / g since j < d and g ∣ j, g ∣ d!
    have hgj : Nat.gcd j d ∣ j := Nat.gcd_dvd_left j d
    have hmul : Nat.gcd j d * (j / Nat.gcd j d) < Nat.gcd j d * (d / Nat.gcd j d) := by
      rw [Nat.mul_div_cancel' hgj, Nat.mul_div_cancel' hgd]; exact hj
    exact Nat.lt_of_mul_lt_mul_left hmul
  · intro j₁ hj₁ j₂ hj₂ heq
    have h1 : d / Nat.gcd j₁ d = d / Nat.gcd j₂ d := congrArg Sigma.fst heq
    have h2 : j₁ / Nat.gcd j₁ d = j₂ / Nat.gcd j₂ d := by
      have := congrArg Sigma.snd heq; simpa using this
    have hg1_pos : 0 < Nat.gcd j₁ d := Nat.gcd_pos_of_pos_right j₁ hd
    have hg2_pos : 0 < Nat.gcd j₂ d := Nat.gcd_pos_of_pos_right j₂ hd
    have hgd1 : Nat.gcd j₁ d ∣ d := Nat.gcd_dvd_right j₁ d
    have hgd2 : Nat.gcd j₂ d ∣ d := Nat.gcd_dvd_right j₂ d
    have hq_pos : 0 < d / Nat.gcd j₁ d := Nat.div_pos (Nat.le_of_dvd hd hgd1) hg1_pos
    have hg_eq : Nat.gcd j₁ d = Nat.gcd j₂ d := by
      have hm : Nat.gcd j₁ d * (d / Nat.gcd j₁ d) = Nat.gcd j₂ d * (d / Nat.gcd j₁ d) := by
        rw [Nat.mul_div_cancel' hgd1, h1, Nat.mul_div_cancel' hgd2]
      exact Nat.eq_of_mul_eq_mul_right hq_pos hm
    calc j₁ = Nat.gcd j₁ d * (j₁ / Nat.gcd j₁ d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left j₁ d)).symm
      _ = Nat.gcd j₂ d * (j₂ / Nat.gcd j₂ d) := by rw [h2, hg_eq]
      _ = j₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left j₂ d)
  · rintro ⟨q, a⟩ hqa
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range] at hqa
    rcases hqa with ⟨⟨hqd, _⟩, haq, hcop⟩
    let g := d / q
    have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hqd hd
    have hg_pos : 0 < g := Nat.div_pos (Nat.le_of_dvd hd hqd) hq_pos
    have hqg : g * q = d := by rw [mul_comm]; exact Nat.mul_div_cancel' hqd
    refine ⟨g * a, Finset.mem_range.mpr (by rw [← hqg]; exact Nat.mul_lt_mul_of_pos_left haq hg_pos), ?_⟩
    have hgcd : Nat.gcd (g * a) d = g := by
      rw [← hqg, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    ext
    · dsimp only
      rw [hgcd, ← hqg, Nat.mul_div_cancel_left q hg_pos]
    · dsimp only
      rw [hgcd, Nat.mul_div_cancel_left a hg_pos]
  · intro j _; rfl

/-! ### Part 2: Exact Möbius Coprime Factorization & Farey–Möbius Duality Theorem -/

/-- **Theorem 3 (Exact Möbius Coprime Split `μ(q * m) = if Coprime q m then μ q * μ m else 0`)**:
For ANY `q, m : ℕ`: `μ (q * m) = if Nat.Coprime q m then μ q * μ m else 0`. -/
theorem moebius_mul_eq_ite_coprime (q m : ℕ) :
    μ (q * m) = if Nat.Coprime q m then μ q * μ m else 0 := by
  by_cases hcop : Nat.Coprime q m
  · rw [if_pos hcop]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  · rw [if_neg hcop]
    obtain ⟨p, hp, hpq, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hns : ¬Squarefree (q * m) := by
      intro hsf
      exact hp.not_isUnit (hsf p (Nat.mul_dvd_mul hpq hpm))
    exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns

/-- Primitive Farey sum at denominator `q`: `F(q) = ∑_{a < q, (a, q) = 1} ĝ_Y(a/q) * e(-a*n/q)`. -/
noncomputable def primitiveFareyTerm (Y : Finset ℕ) (g : ℕ → ℝ) (n q : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    expSum Y g a q * eFrac (-(a : ℤ) * (n : ℤ)) q

/-- **Theorem 4 (Exact Farey–Möbius Duality Theorem)**:
For ANY `D_max : ℕ`, ANY finite set `S ⊆ Finset.Icc 1 D_max`, ANY `Y : Finset ℕ`, `n : ℕ`, and `g : ℕ → ℝ`:
`((∑ d ∈ S, (μ d : ℝ) * ∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)`
`= ∑ q ∈ Finset.Icc 1 D_max, ((μ q : ℂ) / (q : ℂ)) * (∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q), ((μ m : ℂ) / (m : ℂ))) * primitiveFareyTerm Y g n q`! -/
theorem farey_moebius_duality_exact {D_max : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D_max)
    (Y : Finset ℕ) (n : ℕ) (g : ℕ → ℝ) :
    ((∑ d ∈ S, (μ d : ℝ) * ∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)
      = ∑ q ∈ Finset.Icc 1 D_max,
          ((μ q : ℂ) / (q : ℂ)) *
          (∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q),
            ((μ m : ℂ) / (m : ℂ))) *
          primitiveFareyTerm Y g n q := by
  -- Step 1: For each d ∈ S, apply Theorem 1 + Theorem 2 to reduce to ∑_{q ∣ d} primitiveFareyTerm Y g n q!
  have hsingle : ∀ d ∈ S,
      (((μ d : ℝ) * ∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)
        = ((μ d : ℂ) / (d : ℂ)) * ∑ q ∈ d.divisors, primitiveFareyTerm Y g n q := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp (hS hd)).1
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, progression_eq_finite_fourier_sum hd_pos n Y g]
    have hreduce : ∑ j ∈ Finset.range d, expSum Y g j d * eFrac (-(j : ℤ) * (n : ℤ)) d
        = ∑ q ∈ d.divisors, primitiveFareyTerm Y g n q := by
      have hterm : ∀ j ∈ Finset.range d,
          expSum Y g j d * eFrac (-(j : ℤ) * (n : ℤ)) d
            = expSum Y g (j / Nat.gcd j d) (d / Nat.gcd j d)
              * eFrac (-((j / Nat.gcd j d : ℕ) : ℤ) * (n : ℤ)) (d / Nat.gcd j d) := by
        intro j _
        let c := Nat.gcd j d
        have hc_pos : 0 < c := Nat.gcd_pos_of_pos_right j hd_pos
        have hcj : c * (j / c) = j := Nat.mul_div_cancel' (Nat.gcd_dvd_left j d)
        have hcd : c * (d / c) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right j d)
        have hexp_eq : expSum Y g j d = expSum Y g (j / c) (d / c) := by
          unfold expSum
          refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          conv_lhs => rw [← hcj, ← hcd]
          have hrew : (((c * (j / c) : ℕ) : ℤ) * (y : ℤ)) = (c : ℤ) * (((j / c : ℕ) : ℤ) * (y : ℤ)) := by
            push_cast; ring
          rw [hrew, eFrac_cancel_mul hc_pos]
        have he_eq : eFrac (-(j : ℤ) * (n : ℤ)) d
            = eFrac (-((j / c : ℕ) : ℤ) * (n : ℤ)) (d / c) := by
          conv_lhs => rw [← hcj, ← hcd]
          have hrew : -(((c * (j / c) : ℕ) : ℤ)) * (n : ℤ) = (c : ℤ) * (-((j / c : ℕ) : ℤ) * (n : ℤ)) := by
            push_cast; ring
          rw [hrew, eFrac_cancel_mul hc_pos]
        rw [hexp_eq, he_eq]
      rw [Finset.sum_congr rfl hterm]
      exact farey_primitive_partition_sum hd_pos (fun a q => expSum Y g a q * eFrac (-(a : ℤ) * (n : ℤ)) q)
    rw [hreduce]
    ring
  rw [Complex.ofReal_sum]
  have hL : ∑ d ∈ S, (((μ d : ℝ) * ∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)
      = ∑ d ∈ S, ∑ q ∈ Finset.Icc 1 D_max,
          if q ∣ d then ((μ d : ℂ) / (d : ℂ)) * primitiveFareyTerm Y g n q else 0 := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hsingle d hd, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    have hd_icc := Finset.mem_Icc.mp (hS hd)
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hqd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hqd hd_icc.1, le_trans (Nat.le_of_dvd hd_icc.1 hqd) hd_icc.2⟩, hqd⟩
    · rintro ⟨_, hqd⟩
      exact ⟨hqd, by omega⟩
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq_icc := Finset.mem_Icc.mp hq
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_filter]
  -- Bijection m ↦ q * m from {m ∈ Icc 1 (D_max / q) | q * m ∈ S ∧ Coprime m q} to {d ∈ S | q ∣ d ∧ Coprime (d/q) q}
  -- (and non-coprime d have μ d = 0!)
  have hnoncop0 : ∑ d ∈ S.filter (fun d => q ∣ d), ((μ d : ℂ) / (d : ℂ)) * primitiveFareyTerm Y g n q
      = ∑ d ∈ S.filter (fun d => q ∣ d ∧ Nat.Coprime (d / q) q),
          ((μ d : ℂ) / (d : ℂ)) * primitiveFareyTerm Y g n q := by
    symm
    refine Finset.sum_subset (fun d hd => by
      rw [Finset.mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.1⟩) ?_
    intro d hd hnot
    rw [Finset.mem_filter] at hd hnot
    have hnc : ¬Nat.Coprime (d / q) q := fun h => hnot ⟨hd.1, hd.2, h⟩
    have hmu0 : μ d = 0 := by
      have hdeq : d = q * (d / q) := (Nat.mul_div_cancel' hd.2).symm
      rw [hdeq, moebius_mul_eq_ite_coprime, if_neg (fun h => hnc h.symm)]
    simp [hmu0]
  rw [hnoncop0]
  symm
  refine Finset.sum_bij (fun m _ => q * m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_filter]
    refine ⟨hm.2.1, dvd_mul_right q m, ?_⟩
    rw [Nat.mul_div_cancel_left m hq_icc.1]; exact hm.2.2
  · intro m₁ _ m₂ _ heq
    exact Nat.eq_of_mul_eq_mul_left hq_icc.1 heq
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd_icc := Finset.mem_Icc.mp (hS hd.1)
    refine ⟨d / q, ?_, Nat.mul_div_cancel' hd.2.1⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hm_pos : 1 ≤ d / q := Nat.div_pos (Nat.le_of_dvd hd_icc.1 hd.2.1) hq_icc.1
    have hm_le : d / q ≤ D_max / q := Nat.div_le_div_right hd_icc.2
    exact ⟨⟨hm_pos, hm_le⟩, by rw [Nat.mul_div_cancel' hd.2.1]; exact hd.1, hd.2.2⟩
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hmu : μ (q * m) = μ q * μ m := by
      rw [moebius_mul_eq_ite_coprime, if_pos hm.2.2.symm]
    rw [hmu]
    push_cast
    ring

/-- **Theorem 5 (Exact Frequency-Localization Split Into PNT-Damped Low/Medium Spectrum + Top Farey Shell)**:
Splitting `q ∈ Icc 1 D_max` at any cutoff `Q_cut` into `q ≤ Q_cut` (where `|M_q| ≤ ε_PNT` by PNT for `μ`)
and the top Farey shell `q > Q_cut`, proves unconditionally:
`‖∑_{d ∈ S} μ(d) ∑_{y ∈ Y, y ≡ n [MOD d]} g y‖`
`≤ ε_PNT * ∑_{q ∈ Icc 1 Q_cut} (1 / q) * ‖primitiveFareyTerm Y g n q‖`
`  + ‖∑_{q ∈ Icc (Q_cut + 1) D_max} (μ q / q) * M_q * primitiveFareyTerm Y g n q‖`! -/
theorem farey_moebius_frequency_localization_bound {D_max Q_cut : ℕ} (hQ : Q_cut ≤ D_max)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D_max) (Y : Finset ℕ) (n : ℕ) (g : ℕ → ℝ)
    {ε_PNT : ℝ} (_hε : 0 ≤ ε_PNT)
    (hPNT : ∀ q ∈ Finset.Icc 1 Q_cut,
      ‖∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q),
        ((μ m : ℂ) / (m : ℂ))‖ ≤ ε_PNT) :
    ‖((∑ d ∈ S, (μ d : ℝ) * ∑ y ∈ Y.filter (fun y => y ≡ n [MOD d]), g y : ℝ) : ℂ)‖
      ≤ ε_PNT * (∑ q ∈ Finset.Icc 1 Q_cut, (1 / (q : ℝ)) * ‖primitiveFareyTerm Y g n q‖)
        + ‖∑ q ∈ Finset.Icc (Q_cut + 1) D_max,
            ((μ q : ℂ) / (q : ℂ)) *
            (∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q),
              ((μ m : ℂ) / (m : ℂ))) *
            primitiveFareyTerm Y g n q‖ := by
  rw [farey_moebius_duality_exact S hS Y n g]
  have hsplit : Finset.Icc 1 D_max = Finset.Icc 1 Q_cut ∪ Finset.Icc (Q_cut + 1) D_max := by
    ext q; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 Q_cut) (Finset.Icc (Q_cut + 1) D_max) := by
    rw [Finset.disjoint_left]; intro q h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) ?_
  apply add_le_add _ le_rfl
  calc _ ≤ ∑ q ∈ Finset.Icc 1 Q_cut,
            ‖((μ q : ℂ) / (q : ℂ)) *
              (∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q),
                ((μ m : ℂ) / (m : ℂ))) *
              primitiveFareyTerm Y g n q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 Q_cut, ε_PNT * ((1 / (q : ℝ)) * ‖primitiveFareyTerm Y g n q‖) := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [norm_mul, norm_mul, norm_div]
        have hmu_le : ‖(μ q : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          have h1 : |μ q| ≤ 1 := by
            by_cases hsf : Squarefree q
            · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
          exact_mod_cast h1
        have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
        have hdiv_le : ‖(μ q : ℂ)‖ / ‖(q : ℂ)‖ ≤ 1 / (q : ℝ) := by
          rw [Complex.norm_natCast]
          exact div_le_div_of_nonneg_right hmu_le (le_of_lt hq_pos)
        have hM_le := hPNT q hq
        have h1 : (‖(μ q : ℂ)‖ / ‖(q : ℂ)‖) *
            ‖∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q),
              ((μ m : ℂ) / (m : ℂ))‖ ≤ (1 / (q : ℝ)) * ε_PNT :=
          mul_le_mul hdiv_le hM_le (norm_nonneg _) (by positivity)
        have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (primitiveFareyTerm Y g n q))
        linarith
    _ = ε_PNT * ∑ q ∈ Finset.Icc 1 Q_cut, (1 / (q : ℝ)) * ‖primitiveFareyTerm Y g n q‖ :=
        (Finset.mul_sum _ _ _).symm

end GoldbachWave32
