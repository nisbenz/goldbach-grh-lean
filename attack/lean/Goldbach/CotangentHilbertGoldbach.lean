import Mathlib

/-!
# Wave 37 — Exact Real Cotangent–Hilbert Identity for Goldbach & Pure-Integer Sawtooth Evaluation

Building directly on Waves 33–36, this file proves the **exact, zero-complex-number Cotangent–Hilbert
Transform Identity** for the Goldbach self-convolution of ANY Ramanujan-expanded arithmetical function
`f(x) = ∑_{q=1}^Q α_q c_q(x)` (including Selberg's `Λ_R`, `PureSquare` `F_{(M, n]}`, and exact von
Mangoldt `Λ`), together with the **exact pure-integer sawtooth evaluation** of the cotangent–sine
kernel and the **exact Gauss–Eisenstein cotangent multiplication identity**:

1. **Exact Symmetrized Cotangent Kernel Identity (`symmetrized_geom_kernel_eq_cot`)**:
   For any `n : ℕ` and any `θ, φ : ℝ` with `Real.sin (Real.pi * (θ - φ)) ≠ 0`:
   `(eReal (n * φ) * geomExpSum n (θ - φ) + eReal (n * θ) * geomExpSum n (φ - θ)).re`
   `= (Real.sin (2 * Real.pi * n * θ) - Real.sin (2 * Real.pi * n * φ)) * cotPi (θ - φ)`.

2. **Exact Real Cotangent–Hilbert Identity for `offDiagFareyForm` (`offDiagFareyForm_re_eq_cotangent_hilbert`)**:
   For ANY `n, Q : ℕ` and ANY real Ramanujan spectrum `α : ℕ → ℝ`:
   `(offDiagFareyForm n Q α α).re`
   `= ∑ q₁ ∈ Icc 1 Q, α q₁ * ∑ a₁ ∈ coprime q₁, Real.sin (2 * π * n * a₁ / q₁) * H_Q[α](a₁ / q₁)`,
   factoring **100% of the `n`-dependence** out of the Farey–Hilbert transform `H_Q[α](a₁ / q₁)`!

3. **Exact Pure-Integer Sawtooth Evaluation (`sin_cot_sum_eq_sawtooth_exact`)**:
   For EVERY `1 ≤ q` and EVERY `r : ℕ`:
   `∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * r * b / q) * cotPi (b / q)`
   `= if q ∣ r then 0 else (q : ℝ) - 2 * ((r % q : ℕ) : ℝ)`!
   Proved completely elementarily by exact trigonometric telescoping (`sin(2π(r+1)θ) - sin(2π r θ) =
   2 cos(π(2r+1)θ) sin(π θ)`, cancelling `sin(π θ)` identically!).

4. **Exact Gauss–Eisenstein Cotangent Multiplication Identity (`eisenstein_cotangent_sum_exact`)**:
   For EVERY `0 < d` and EVERY `x : ℝ` with `Real.sin (Real.pi * d * x) ≠ 0`:
   `∑ j ∈ Finset.range d, cotPi (x - (j : ℝ) / d) = (d : ℝ) * cotPi ((d : ℝ) * x)`.
   Proved from first principles via the logarithmic derivative of `∏_{j < d} (z - e(j/d)) = z^d - 1`!
-/

open scoped BigOperators
open ArithmeticFunction

namespace GoldbachWave37

/-- Normalized cotangent `cot(π u) = cos(π u) / sin(π u)`. -/
noncomputable def cotPi (u : ℝ) : ℝ :=
  Real.cos (Real.pi * u) / Real.sin (Real.pi * u)

/-- Additive character `e(θ) = exp(2π i θ)`. -/
noncomputable def eReal (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))

/-- Rational additive character `e(m / q)`. -/
noncomputable def eFrac (m : ℤ) (q : ℕ) : ℂ :=
  eReal ((m : ℝ) / (q : ℝ))

/-- Finite geometric exponential sum `G_n(θ) = ∑_{x=0}^{n-1} e(x θ)`. -/
noncomputable def geomExpSum (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ x ∈ Finset.range n, eReal ((x : ℝ) * θ)

/-- Exact off-diagonal Farey aliasing form (matching Waves 34 & 36). -/
noncomputable def offDiagFareyForm (n Q : ℕ) (α β : ℕ → ℝ) : ℂ :=
  ∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q,
    ((α q₁ * β q₂ : ℝ) : ℂ) *
      ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
        ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
          if (q₁, a₁) = (q₂, a₂) then 0
          else eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)

/-- Discrete `n`-independent Farey–Hilbert transform `H_Q[α](q₁, a₁)`. -/
noncomputable def fareyHilbertTransform (Q : ℕ) (α : ℕ → ℝ) (q₁ a₁ : ℕ) : ℝ :=
  ∑ q₂ ∈ Finset.Icc 1 Q, α q₂ *
    ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
      if (q₁, a₁) = (q₂, a₂) then 0 else cotPi ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)

/-! ### Private Helpers -/

private lemma cotPi_neg (u : ℝ) : cotPi (-u) = -cotPi u := by
  unfold cotPi
  rw [mul_neg, Real.cos_neg, Real.sin_neg, div_neg]

private lemma eReal_add (θ₁ θ₂ : ℝ) : eReal (θ₁ + θ₂) = eReal θ₁ * eReal θ₂ := by
  unfold eReal; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma eReal_neg (θ : ℝ) : eReal (-θ) = (eReal θ)⁻¹ := by
  unfold eReal; rw [← Complex.exp_neg]; congr 1; push_cast; ring

private lemma eReal_pow (θ : ℝ) (x : ℕ) : (eReal θ) ^ x = eReal ((x : ℝ) * θ) := by
  induction x with
  | zero => unfold eReal; simp
  | succ x ih =>
    rw [pow_succ, ih]; unfold eReal; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma eReal_eq_cos_add_sin (θ : ℝ) :
    eReal θ = (Real.cos (2 * Real.pi * θ) : ℂ) + (Real.sin (2 * Real.pi * θ) : ℂ) * Complex.I := by
  unfold eReal
  have h : 2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- Exact Cayley identity `(e(u) + 1) / (e(u) - 1) = -i * cot(π u)` whenever `sin(π u) ≠ 0`. -/
private lemma cayley_eReal_eq_neg_I_cotPi {u : ℝ} (hsin : Real.sin (Real.pi * u) ≠ 0) :
    eReal u ≠ 1 ∧ (eReal u + 1) / (eReal u - 1) = -Complex.I * (cotPi u : ℂ) := by
  let z : ℂ := ((Real.pi * u : ℝ) : ℂ) * Complex.I
  have hz2 : eReal u = Complex.exp z * Complex.exp z := by
    unfold eReal; rw [← Complex.exp_add]; congr 1; dsimp only [z]; push_cast; ring
  have hz_inv : Complex.exp z * Complex.exp (-z) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hdiff : Complex.exp z - Complex.exp (-z) = 2 * Complex.I * (Real.sin (Real.pi * u) : ℂ) := by
    rw [Complex.ofReal_sin, Complex.sin]
    have hneg : -((Real.pi * u : ℝ) : ℂ) * Complex.I = -z := by dsimp only [z]; ring
    rw [hneg]
    change Complex.exp z - Complex.exp (-z) = 2 * Complex.I * ((Complex.exp (-z) - Complex.exp z) * Complex.I / 2)
    have hmul : 2 * Complex.I * ((Complex.exp (-z) - Complex.exp z) * Complex.I / 2)
        = Complex.I ^ 2 * (Complex.exp (-z) - Complex.exp z) := by ring
    rw [hmul, Complex.I_sq]; ring
  have hsum : Complex.exp z + Complex.exp (-z) = 2 * (Real.cos (Real.pi * u) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    have hneg : -((Real.pi * u : ℝ) : ℂ) * Complex.I = -z := by dsimp only [z]; ring
    rw [hneg]
    change Complex.exp z + Complex.exp (-z) = 2 * ((Complex.exp z + Complex.exp (-z)) / 2)
    ring
  have hnum : eReal u + 1 = Complex.exp z * (2 * (Real.cos (Real.pi * u) : ℂ)) := by
    rw [hz2, ← hsum, mul_add, hz_inv]
  have hden : eReal u - 1 = Complex.exp z * (2 * Complex.I * (Real.sin (Real.pi * u) : ℂ)) := by
    rw [hz2, ← hdiff, mul_sub, hz_inv]
  have hsinC : (Real.sin (Real.pi * u) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
  have hexp_ne : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  have hden_ne : eReal u - 1 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hexp_ne (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hsinC)
  refine ⟨sub_ne_zero.mp hden_ne, ?_⟩
  rw [hnum, hden]
  unfold cotPi
  rw [Complex.ofReal_div]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  field_simp [hexp_ne, hsinC, Complex.I_ne_zero]
  linear_combination (Real.cos (Real.pi * u) : ℂ) * hI2

/-! ### Theorem 1: Exact Symmetrized Cotangent Kernel Identity -/

/-- **Theorem 1 (Exact Symmetrized Cotangent Kernel Identity)**:
For any `n : ℕ` and any `θ, φ : ℝ` with `Real.sin (Real.pi * (θ - φ)) ≠ 0`:
`(eReal (n * φ) * geomExpSum n (θ - φ) + eReal (n * θ) * geomExpSum n (φ - θ)).re`
`= (Real.sin (2 * Real.pi * n * θ) - Real.sin (2 * Real.pi * n * φ)) * cotPi (θ - φ)`! -/
theorem symmetrized_geom_kernel_eq_cot (n : ℕ) {θ φ : ℝ}
    (hsin : Real.sin (Real.pi * (θ - φ)) ≠ 0) :
    (eReal ((n : ℝ) * φ) * geomExpSum n (θ - φ)
      + eReal ((n : ℝ) * θ) * geomExpSum n (φ - θ)).re
      = (Real.sin (2 * Real.pi * (n : ℝ) * θ) - Real.sin (2 * Real.pi * (n : ℝ) * φ))
        * cotPi (θ - φ) := by
  have ⟨hne, hcay⟩ := cayley_eReal_eq_neg_I_cotPi hsin
  have hne_neg : eReal (φ - θ) ≠ 1 := by
    have hrew : φ - θ = -(θ - φ) := by ring
    rw [hrew, eReal_neg]
    intro hinv
    have : eReal (θ - φ) = 1 := inv_eq_one.mp hinv
    exact hne this
  have hG1 : geomExpSum n (θ - φ) = (eReal ((n : ℝ) * (θ - φ)) - 1) / (eReal (θ - φ) - 1) := by
    unfold geomExpSum
    have hrew : ∀ x ∈ Finset.range n, eReal ((x : ℝ) * (θ - φ)) = (eReal (θ - φ)) ^ x :=
      fun x _ => (eReal_pow (θ - φ) x).symm
    rw [Finset.sum_congr rfl hrew, geom_sum_eq hne, eReal_pow]
  have hG2 : geomExpSum n (φ - θ) = (eReal ((n : ℝ) * (φ - θ)) - 1) / (eReal (φ - θ) - 1) := by
    unfold geomExpSum
    have hrew : ∀ x ∈ Finset.range n, eReal ((x : ℝ) * (φ - θ)) = (eReal (φ - θ)) ^ x :=
      fun x _ => (eReal_pow (φ - θ) x).symm
    rw [Finset.sum_congr rfl hrew, geom_sum_eq hne_neg, eReal_pow]
  have hnum1 : eReal ((n : ℝ) * φ) * (eReal ((n : ℝ) * (θ - φ)) - 1)
      = eReal ((n : ℝ) * θ) - eReal ((n : ℝ) * φ) := by
    rw [mul_sub, mul_one, ← eReal_add]; congr 2; ring
  have hnum2 : eReal ((n : ℝ) * θ) * (eReal ((n : ℝ) * (φ - θ)) - 1)
      = -(eReal ((n : ℝ) * θ) - eReal ((n : ℝ) * φ)) := by
    rw [mul_sub, mul_one, ← eReal_add]
    have hadd : (n : ℝ) * θ + (n : ℝ) * (φ - θ) = (n : ℝ) * φ := by ring
    rw [hadd]; ring
  have hcomb : eReal ((n : ℝ) * φ) * geomExpSum n (θ - φ) + eReal ((n : ℝ) * θ) * geomExpSum n (φ - θ)
      = (eReal ((n : ℝ) * θ) - eReal ((n : ℝ) * φ)) * (-Complex.I * (cotPi (θ - φ) : ℂ)) := by
    rw [hG1, hG2, ← mul_div_assoc, ← mul_div_assoc, hnum1, hnum2, ← hcay]
    have hneg_e : eReal (φ - θ) = (eReal (θ - φ))⁻¹ := by
      rw [show φ - θ = -(θ - φ) by ring, eReal_neg]
    rw [hneg_e]
    have hz_ne : eReal (θ - φ) ≠ 0 := Complex.exp_ne_zero _
    have hz1_ne : eReal (θ - φ) - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hinv1_ne : (eReal (θ - φ))⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (by rwa [← hneg_e])
    field_simp [hz_ne, hz1_ne, hinv1_ne]
    ring
  rw [hcomb, eReal_eq_cos_add_sin ((n : ℝ) * θ), eReal_eq_cos_add_sin ((n : ℝ) * φ)]
  simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.sub_im, Complex.add_im,
    Complex.mul_im]
  have h1 : 2 * Real.pi * ((n : ℝ) * θ) = 2 * Real.pi * (n : ℝ) * θ := by ring
  have h2 : 2 * Real.pi * ((n : ℝ) * φ) = 2 * Real.pi * (n : ℝ) * φ := by ring
  rw [h1, h2]
  ring

/-! ### Theorem 2: Exact Real Cotangent–Hilbert Transform Identity for `offDiagFareyForm` -/

private lemma coprime_frac_eq_iff {q₁ q₂ a₁ a₂ : ℕ} (_hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂) :
    a₁ * q₂ = a₂ * q₁ ↔ q₁ = q₂ ∧ a₁ = a₂ := by
  constructor
  · intro heq
    have h1 : q₁ ∣ a₁ * q₂ := by rw [heq]; exact dvd_mul_left q₁ a₂
    have hq1_dvd : q₁ ∣ q₂ := hcop₁.symm.dvd_of_dvd_mul_left h1
    have h2 : q₂ ∣ a₂ * q₁ := by rw [← heq]; exact dvd_mul_left q₂ a₁
    have hq2_dvd : q₂ ∣ q₁ := hcop₂.symm.dvd_of_dvd_mul_left h2
    have hqeq : q₁ = q₂ := Nat.dvd_antisymm hq1_dvd hq2_dvd
    refine ⟨hqeq, ?_⟩
    rw [hqeq] at heq
    exact Nat.eq_of_mul_eq_mul_right hq₂ heq
  · rintro ⟨rfl, rfl⟩; rfl

private lemma sin_pi_farey_diff_ne_zero {q₁ q₂ a₁ a₂ : ℕ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (ha₁ : a₁ < q₁) (ha₂ : a₂ < q₂)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Real.sin (Real.pi * ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)) ≠ 0 := by
  intro hsin0
  rw [Real.sin_eq_zero_iff] at hsin0
  rcases hsin0 with ⟨k, hk⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfrac : (a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂ = (k : ℝ) := by
    have : Real.pi * ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂) = Real.pi * (k : ℝ) := by linarith
    exact mul_left_cancel₀ hpi this
  have hq1R : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr hq₁
  have hq2R : (0 : ℝ) < (q₂ : ℝ) := Nat.cast_pos.mpr hq₂
  have hlt1 : (a₁ : ℝ) / q₁ < 1 := (div_lt_one hq1R).mpr (by exact_mod_cast ha₁)
  have hlt2 : (a₂ : ℝ) / q₂ < 1 := (div_lt_one hq2R).mpr (by exact_mod_cast ha₂)
  have hnn1 : (0 : ℝ) ≤ (a₁ : ℝ) / q₁ := by positivity
  have hnn2 : (0 : ℝ) ≤ (a₂ : ℝ) / q₂ := by positivity
  have hk0 : k = 0 := by
    have hk_lt : (k : ℝ) < 1 := by linarith
    have hk_gt : (-1 : ℝ) < (k : ℝ) := by linarith
    have hk1 : k < 1 := by exact_mod_cast hk_lt
    have hk2 : -1 < k := by exact_mod_cast hk_gt
    omega
  rw [hk0, Int.cast_zero, sub_eq_zero] at hfrac
  have hmulR : (a₁ : ℝ) * (q₂ : ℝ) = (a₂ : ℝ) * (q₁ : ℝ) := by
    have h := (div_eq_div_iff (ne_of_gt hq1R) (ne_of_gt hq2R)).mp hfrac
    linarith
  have hmulN : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast hmulR
  have ⟨h1, h2⟩ := (coprime_frac_eq_iff hq₁ hq₂ hcop₁ hcop₂).mp hmulN
  exact hne (Prod.ext h1 h2)

/-- **Theorem 2 (Exact Real Cotangent–Hilbert Transform Identity for Goldbach)**:
For ANY `n, Q : ℕ` and ANY real Ramanujan coefficients `α : ℕ → ℝ`:
`(offDiagFareyForm n Q α α).re`
`= ∑ q₁ ∈ Finset.Icc 1 Q, α q₁ * ∑ a₁ ∈ (Finset.range q₁).filter (Nat.Coprime · q₁),`
`    Real.sin (2 * Real.pi * (n : ℝ) * ((a₁ : ℝ) / q₁)) * fareyHilbertTransform Q α q₁ a₁`!
Factoring `100%` of the `n`-dependence outside the Farey–Hilbert transform! -/
theorem offDiagFareyForm_re_eq_cotangent_hilbert (n Q : ℕ) (α : ℕ → ℝ) :
    (offDiagFareyForm n Q α α).re
      = ∑ q₁ ∈ Finset.Icc 1 Q, α q₁ *
          ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            Real.sin (2 * Real.pi * (n : ℝ) * ((a₁ : ℝ) / q₁))
              * fareyHilbertTransform Q α q₁ a₁ := by
  -- Define F as the Farey pair Finset of order Q!
  let F := (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
  have hL : (offDiagFareyForm n Q α α).re
      = ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else (eReal ((n : ℝ) * ((p₂.2 : ℝ) / p₂.1)) *
               geomExpSum n ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)).re) := by
    unfold offDiagFareyForm
    rw [Complex.re_sum]
    have hstep1 : ∑ q₁ ∈ Finset.Icc 1 Q,
          (∑ q₂ ∈ Finset.Icc 1 Q, ((α q₁ * α q₂ : ℝ) : ℂ) *
            ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                if (q₁, a₁) = (q₂, a₂) then 0
                else eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)).re
        = ∑ q₁ ∈ Finset.Icc 1 Q, ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ q₂ ∈ Finset.Icc 1 Q, ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            (α q₁ * α q₂) *
              (if (q₁, a₁) = (q₂, a₂) then (0 : ℝ)
               else (eReal ((n : ℝ) * ((a₂ : ℝ) / q₂)) *
                 geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)).re) := by
      refine Finset.sum_congr rfl fun q₁ _ => ?_
      rw [Complex.re_sum]
      calc ∑ q₂ ∈ Finset.Icc 1 Q,
            (((α q₁ * α q₂ : ℝ) : ℂ) *
              ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
                ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                  if (q₁, a₁) = (q₂, a₂) then 0
                  else eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)).re
          = ∑ q₂ ∈ Finset.Icc 1 Q, ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                (α q₁ * α q₂) *
                  (if (q₁, a₁) = (q₂, a₂) then (0 : ℝ)
                   else (eReal ((n : ℝ) * ((a₂ : ℝ) / q₂)) *
                     geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)).re) := by
              refine Finset.sum_congr rfl fun q₂ _ => ?_
              rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a₁ _ => ?_
              rw [Complex.re_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a₂ _ => ?_
              split_ifs
              · simp
              · congr 2; unfold eFrac; congr 1; push_cast; ring
        _ = _ := Finset.sum_comm
    rw [hstep1]
    rw [Finset.sum_sigma']
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.sum_sigma']
  have hR : ∑ q₁ ∈ Finset.Icc 1 Q, α q₁ *
          ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            Real.sin (2 * Real.pi * (n : ℝ) * ((a₁ : ℝ) / q₁))
              * fareyHilbertTransform Q α q₁ a₁
      = ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else Real.sin (2 * Real.pi * (n : ℝ) * ((p₁.2 : ℝ) / p₁.1))
               * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)) := by
    have h1 : ∑ q₁ ∈ Finset.Icc 1 Q, α q₁ *
          ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            Real.sin (2 * Real.pi * (n : ℝ) * ((a₁ : ℝ) / q₁))
              * fareyHilbertTransform Q α q₁ a₁
        = ∑ q₁ ∈ Finset.Icc 1 Q, ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ q₂ ∈ Finset.Icc 1 Q, ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            (α q₁ * α q₂) *
              (if (q₁, a₁) = (q₂, a₂) then (0 : ℝ)
               else Real.sin (2 * Real.pi * (n : ℝ) * ((a₁ : ℝ) / q₁))
                 * cotPi ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)) := by
      refine Finset.sum_congr rfl fun q₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      unfold fareyHilbertTransform
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q₂ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a₂ _ => by split_ifs <;> ring
    rw [h1, Finset.sum_sigma']
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    rw [Finset.sum_sigma']
  -- Symmetrize both sides via Finset.sum_comm and apply Theorem 1!
  rw [hL, hR]
  have h2L : 2 * (∑ p₁ ∈ F, ∑ p₂ ∈ F,
        (α p₁.1 * α p₂.1) *
          (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
           else (eReal ((n : ℝ) * ((p₂.2 : ℝ) / p₂.1)) *
             geomExpSum n ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)).re))
      = ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else (Real.sin (2 * Real.pi * (n : ℝ) * ((p₁.2 : ℝ) / p₁.1))
               - Real.sin (2 * Real.pi * (n : ℝ) * ((p₂.2 : ℝ) / p₂.1)))
               * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)) := by
    have hswap : ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else (eReal ((n : ℝ) * ((p₂.2 : ℝ) / p₂.1)) *
               geomExpSum n ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)).re)
        = ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else (eReal ((n : ℝ) * ((p₁.2 : ℝ) / p₁.1)) *
               geomExpSum n ((p₂.2 : ℝ) / p₂.1 - (p₁.2 : ℝ) / p₁.1)).re) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
      rw [mul_comm (α p₂.1) (α p₁.1)]
      congr 1
      by_cases heq : (p₁.1, p₁.2) = (p₂.1, p₂.2)
      · simp [heq]
      · simp [heq, Ne.symm heq]
    calc 2 * _ = (∑ p₁ ∈ F, ∑ p₂ ∈ F, _) + (∑ p₁ ∈ F, ∑ p₂ ∈ F, _) := two_mul _
      _ = (∑ p₁ ∈ F, ∑ p₂ ∈ F,
            (α p₁.1 * α p₂.1) *
              (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
               else (eReal ((n : ℝ) * ((p₂.2 : ℝ) / p₂.1)) *
                 geomExpSum n ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)).re))
          + (∑ p₁ ∈ F, ∑ p₂ ∈ F,
              (α p₁.1 * α p₂.1) *
                (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
                 else (eReal ((n : ℝ) * ((p₁.2 : ℝ) / p₁.1)) *
                   geomExpSum n ((p₂.2 : ℝ) / p₂.1 - (p₁.2 : ℝ) / p₁.1)).re)) := by
            congr 1
      _ = _ := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p₂ hp₂ => ?_
            rw [← mul_add]
            congr 1
            by_cases heq : (p₁.1, p₁.2) = (p₂.1, p₂.2)
            · simp [heq]
            · simp only [heq, ↓reduceIte]
              rw [← Complex.add_re]
              have hm1 := Finset.mem_sigma.mp hp₁
              have hm2 := Finset.mem_sigma.mp hp₂
              have hf1 := Finset.mem_filter.mp hm1.2
              have hf2 := Finset.mem_filter.mp hm2.2
              have hsin := sin_pi_farey_diff_ne_zero
                (Finset.mem_Icc.mp hm1.1).1 (Finset.mem_Icc.mp hm2.1).1
                (Finset.mem_range.mp hf1.1) (Finset.mem_range.mp hf2.1)
                hf1.2 hf2.2 heq
              exact symmetrized_geom_kernel_eq_cot n hsin
  have h2R : 2 * (∑ p₁ ∈ F, ∑ p₂ ∈ F,
        (α p₁.1 * α p₂.1) *
          (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
           else Real.sin (2 * Real.pi * (n : ℝ) * ((p₁.2 : ℝ) / p₁.1))
             * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)))
      = ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else (Real.sin (2 * Real.pi * (n : ℝ) * ((p₁.2 : ℝ) / p₁.1))
               - Real.sin (2 * Real.pi * (n : ℝ) * ((p₂.2 : ℝ) / p₂.1)))
               * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)) := by
    have hswap : ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else Real.sin (2 * Real.pi * (n : ℝ) * ((p₁.2 : ℝ) / p₁.1))
               * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1))
        = ∑ p₁ ∈ F, ∑ p₂ ∈ F,
          (α p₁.1 * α p₂.1) *
            (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
             else -(Real.sin (2 * Real.pi * (n : ℝ) * ((p₂.2 : ℝ) / p₂.1))
               * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => ?_
      rw [mul_comm (α p₂.1) (α p₁.1)]
      congr 1
      by_cases heq : (p₁.1, p₁.2) = (p₂.1, p₂.2)
      · simp [heq]
      · simp only [heq, Ne.symm heq, ↓reduceIte]
        have hneg : (p₂.2 : ℝ) / p₂.1 - (p₁.2 : ℝ) / p₁.1 = -((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1) := by ring
        rw [hneg, cotPi_neg]; ring
    calc 2 * _ = (∑ p₁ ∈ F, ∑ p₂ ∈ F, _) + (∑ p₁ ∈ F, ∑ p₂ ∈ F, _) := two_mul _
      _ = (∑ p₁ ∈ F, ∑ p₂ ∈ F,
            (α p₁.1 * α p₂.1) *
              (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
               else Real.sin (2 * Real.pi * (n : ℝ) * ((p₁.2 : ℝ) / p₁.1))
                 * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)))
          + (∑ p₁ ∈ F, ∑ p₂ ∈ F,
              (α p₁.1 * α p₂.1) *
                (if (p₁.1, p₁.2) = (p₂.1, p₂.2) then (0 : ℝ)
                 else -(Real.sin (2 * Real.pi * (n : ℝ) * ((p₂.2 : ℝ) / p₂.1))
                   * cotPi ((p₁.2 : ℝ) / p₁.1 - (p₂.2 : ℝ) / p₂.1)))) := by congr 1
      _ = _ := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p₁ _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p₂ _ => ?_
            split_ifs <;> ring
  linarith

/-! ### Theorem 3: Exact Pure-Integer Sawtooth Evaluation of `∑_{b=1}^{q-1} sin(2π r b/q) cot(π b/q)` -/

/-- Exact cosine orthogonality `∑_{b=1}^{q-1} cos(2π k b / q) = -1` for `1 ≤ k < q`. -/
private lemma sum_cos_Ico_eq_neg_one {q k : ℕ} (hq : 0 < q) (hk0 : 0 < k) (hkq : k < q) :
    ∑ b ∈ Finset.Ico 1 q, Real.cos (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q)) = -1 := by
  have hne : eReal ((k : ℝ) / q) ≠ 1 := by
    intro h
    unfold eReal at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hmul : (2 : ℂ) * Real.pi * Complex.I * (((k : ℝ) / q : ℝ) : ℂ)
        = (2 : ℂ) * Real.pi * Complex.I * (m : ℂ) := by rw [hm]; ring
    have hdivC : (((k : ℝ) / q : ℝ) : ℂ) = (m : ℂ) := mul_left_cancel₀ hpi hmul
    have hdivR : (k : ℝ) / q = (m : ℝ) := by exact_mod_cast hdivC
    have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
    have hlt1 : (k : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hkq)
    have hgt0 : (0 : ℝ) < (k : ℝ) / q := by positivity
    have hm_lt : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
    have hm_gt : 0 < m := by exact_mod_cast (show (0 : ℝ) < (m : ℝ) by linarith)
    omega
  have hfull : ∑ b ∈ Finset.range q, eReal ((b : ℝ) * ((k : ℝ) / q)) = 0 := by
    have hrew : ∀ b ∈ Finset.range q, eReal ((b : ℝ) * ((k : ℝ) / q)) = (eReal ((k : ℝ) / q)) ^ b :=
      fun b _ => (eReal_pow ((k : ℝ) / q) b).symm
    rw [Finset.sum_congr rfl hrew, geom_sum_eq hne, eReal_pow]
    have htop : eReal ((q : ℝ) * ((k : ℝ) / q)) = 1 := by
      unfold eReal
      have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
      have hc : (q : ℝ) * ((k : ℝ) / q) = (k : ℝ) := by field_simp [hqR]
      rw [hc]
      have harg : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [harg, Complex.exp_nat_mul_two_pi_mul_I]
    simp [htop]
  have hre0 : ∑ b ∈ Finset.range q, Real.cos (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q)) = 0 := by
    have h := congrArg Complex.re hfull
    rw [Complex.zero_re, Complex.re_sum] at h
    have heq : ∀ b ∈ Finset.range q,
        (eReal ((b : ℝ) * ((k : ℝ) / q))).re = Real.cos (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q)) := by
      intro b _
      rw [eReal_eq_cos_add_sin]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      congr 1; ring
    rwa [Finset.sum_congr rfl heq] at h
  have hsplit : Finset.range q = insert 0 (Finset.Ico 1 q) := by
    ext b; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)] at hre0
  simp only [Nat.cast_zero, zero_div, mul_zero, Real.cos_zero] at hre0
  linarith

/-- Exact pointwise trigonometric telescoping identity (zero complex numbers!):
`(sin(2π(r+1)θ) - sin(2π r θ)) * cot(π θ) = cos(2π(r+1)θ) + cos(2π r θ)` whenever `sin(π θ) ≠ 0`! -/
private lemma sin_succ_sub_mul_cotPi (r : ℕ) {θ : ℝ} (hsin : Real.sin (Real.pi * θ) ≠ 0) :
    (Real.sin (2 * Real.pi * ((r + 1 : ℕ) : ℝ) * θ) - Real.sin (2 * Real.pi * (r : ℝ) * θ)) * cotPi θ
      = Real.cos (2 * Real.pi * ((r + 1 : ℕ) : ℝ) * θ) + Real.cos (2 * Real.pi * (r : ℝ) * θ) := by
  unfold cotPi
  have hadd : 2 * Real.pi * ((r + 1 : ℕ) : ℝ) * θ = 2 * Real.pi * (r : ℝ) * θ + 2 * (Real.pi * θ) := by
    push_cast; ring
  rw [hadd, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
  field_simp [hsin]
  have hcs := Real.sin_sq_add_cos_sq (Real.pi * θ)
  linear_combination 2 * Real.sin (2 * Real.pi * (r : ℝ) * θ) * Real.cos (Real.pi * θ) * hcs

/-- **Theorem 3 (Exact Pure-Integer Sawtooth Evaluation of the Cotangent–Sine Kernel)**:
For EVERY `0 < q` and EVERY `r : ℕ`:
`∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * (r : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q)`
`= if q ∣ r then 0 else (q : ℝ) - 2 * ((r % q : ℕ) : ℝ)`! -/
theorem sin_cot_sum_eq_sawtooth_exact {q : ℕ} (hq : 0 < q) (r : ℕ) :
    ∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * (r : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q)
      = if q ∣ r then 0 else (q : ℝ) - 2 * ((r % q : ℕ) : ℝ) := by
  -- First reduce r to r₀ = r % q by 2π-periodicity of sin!
  have hred : ∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * (r : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q)
      = ∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * ((r % q : ℕ) : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    have hdiv : q * (r / q) + r % q = r := Nat.div_add_mod r q
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
    have harg : 2 * Real.pi * (r : ℝ) * ((b : ℝ) / q)
        = 2 * Real.pi * ((r % q : ℕ) : ℝ) * ((b : ℝ) / q) + (((r / q) * b : ℕ) : ℝ) * (2 * Real.pi) := by
      have hdivR : (r : ℝ) = (q : ℝ) * ((r / q : ℕ) : ℝ) + ((r % q : ℕ) : ℝ) := by exact_mod_cast hdiv.symm
      rw [hdivR]; push_cast; field_simp [hqR]; ring
    rw [harg, Real.sin_add_nat_mul_two_pi]
  rw [hred]
  by_cases hqr : q ∣ r
  · rw [if_pos hqr, Nat.mod_eq_zero_of_dvd hqr]
    simp
  · rw [if_neg hqr]
    have hr0_pos : 0 < r % q := Nat.pos_of_ne_zero (fun h => hqr (Nat.dvd_of_mod_eq_zero h))
    have hr0_lt : r % q < q := Nat.mod_lt r hq
    -- Prove by induction on k (1 ≤ k < q) that ∑_{b ∈ Ico 1 q} sin(2π k b / q) cot(π b / q) = q - 2 k!
    have hkey : ∀ k, 1 ≤ k → k < q →
        ∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q)
          = (q : ℝ) - 2 * (k : ℝ) := by
      intro k hk1 hkq
      induction k, hk1 using Nat.le_induction with
      | base =>
        -- Base k = 1: sin(2π θ) cot(π θ) = 2 cos²(π θ) = 1 + cos(2π θ)
        have hpt : ∀ b ∈ Finset.Ico 1 q,
            Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q)
              = 1 + Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * ((b : ℝ) / q)) := by
          intro b hb
          have hb' := Finset.mem_Ico.mp hb
          have hsin : Real.sin (Real.pi * ((b : ℝ) / q)) ≠ 0 := by
            have hlt : Real.pi * ((b : ℝ) / q) < Real.pi := by
              have : (b : ℝ) / q < 1 := (div_lt_one (Nat.cast_pos.mpr hq)).mpr (by exact_mod_cast hb'.2)
              nlinarith [Real.pi_pos]
            have hpos : 0 < Real.pi * ((b : ℝ) / q) := by
              have : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb'.1
              have : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
              positivity
            exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
          unfold cotPi
          have h1 : 2 * Real.pi * ((1 : ℕ) : ℝ) * ((b : ℝ) / q) = 2 * (Real.pi * ((b : ℝ) / q)) := by
            push_cast; ring
          rw [h1, Real.sin_two_mul, Real.cos_two_mul]
          have hmul : 2 * Real.sin (Real.pi * ((b : ℝ) / q)) * Real.cos (Real.pi * ((b : ℝ) / q)) *
              (Real.cos (Real.pi * ((b : ℝ) / q)) / Real.sin (Real.pi * ((b : ℝ) / q)))
              = 2 * Real.cos (Real.pi * ((b : ℝ) / q)) ^ 2 := by
            rw [mul_div_assoc', mul_comm (2 * Real.sin _ * Real.cos _) (Real.cos _)]
            have : Real.cos (Real.pi * ((b : ℝ) / q)) * (2 * Real.sin (Real.pi * ((b : ℝ) / q)) * Real.cos (Real.pi * ((b : ℝ) / q)))
                = (2 * Real.cos (Real.pi * ((b : ℝ) / q)) ^ 2) * Real.sin (Real.pi * ((b : ℝ) / q)) := by ring
            rw [this, mul_div_cancel_right₀ _ hsin]
          rw [hmul]; ring
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
          nsmul_eq_mul, mul_one]
        have hcos := sum_cos_Ico_eq_neg_one hq (by norm_num : 0 < 1) hkq
        have hq1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          simpa using Nat.cast_sub (R := ℝ) (by omega : 1 ≤ q)
        rw [hq1, hcos]; push_cast; ring
      | succ k hk1 ih =>
        have hkq' : k < q := by omega
        have hprev := ih hkq'
        have hdiff : ∑ b ∈ Finset.Ico 1 q,
              (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((b : ℝ) / q))
                - Real.sin (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q))) * cotPi ((b : ℝ) / q)
            = -2 := by
          have hpt : ∀ b ∈ Finset.Ico 1 q,
              (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((b : ℝ) / q))
                - Real.sin (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q))) * cotPi ((b : ℝ) / q)
                = Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((b : ℝ) / q))
                  + Real.cos (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q)) := by
            intro b hb
            have hb' := Finset.mem_Ico.mp hb
            have hsin : Real.sin (Real.pi * ((b : ℝ) / q)) ≠ 0 := by
              have hlt : Real.pi * ((b : ℝ) / q) < Real.pi := by
                have : (b : ℝ) / q < 1 := (div_lt_one (Nat.cast_pos.mpr hq)).mpr (by exact_mod_cast hb'.2)
                nlinarith [Real.pi_pos]
              have hpos : 0 < Real.pi * ((b : ℝ) / q) := by
                have : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb'.1
                have : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
                positivity
              exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
            exact sin_succ_sub_mul_cotPi k hsin
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
            sum_cos_Ico_eq_neg_one hq (by omega) hkq,
            sum_cos_Ico_eq_neg_one hq (by omega) hkq']
          norm_num
        have hsplit : ∑ b ∈ Finset.Ico 1 q,
              (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((b : ℝ) / q))
                - Real.sin (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q))) * cotPi ((b : ℝ) / q)
            = (∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q))
              - (∑ b ∈ Finset.Ico 1 q, Real.sin (2 * Real.pi * (k : ℝ) * ((b : ℝ) / q)) * cotPi ((b : ℝ) / q)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun b _ => by ring
        rw [hsplit, hprev] at hdiff
        push_cast at hdiff ⊢
        linarith
    exact hkey (r % q) hr0_pos hr0_lt

/-! ### Theorem 4: Exact Gauss–Eisenstein Cotangent Multiplication Identity -/

/-- Exact roots-of-unity polynomial factorization `z^d - 1 = ∏_{j < d} (z - e(j / d))` in `ℂ`. -/
private lemma complex_pow_sub_one_eq_prod_eReal {d : ℕ} (hd : 0 < d) (z : ℂ) :
    z ^ d - 1 = ∏ j ∈ Finset.range d, (z - eReal ((j : ℝ) / d)) := by
  -- Use Polynomial factorization in ℂ[X]: P(X) = X^d - 1 and Q(X) = ∏_{j < d} (X - e(j/d)) are monic of degree d
  -- and every e(j/d) is a distinct root of X^d - 1!
  let ω : ℕ → ℂ := fun j => eReal ((j : ℝ) / d)
  have hroot : ∀ j ∈ Finset.range d, (ω j) ^ d = 1 := by
    intro j _
    dsimp only [ω]
    rw [eReal_pow]
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
    have hmul : (d : ℝ) * ((j : ℝ) / d) = (j : ℝ) := by field_simp [hdR]
    rw [hmul]; unfold eReal
    have harg : 2 * (Real.pi : ℂ) * Complex.I * ((j : ℝ) : ℂ) = (j : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_nat_mul_two_pi_mul_I]
  have hinj : Set.InjOn ω (Finset.range d : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
    dsimp only [ω] at heq
    have h1 : eReal ((j₁ : ℝ) / d - (j₂ : ℝ) / d) = 1 := by
      rw [sub_eq_add_neg, eReal_add, eReal_neg, heq]
      unfold eReal; exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
    unfold eReal at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hmul : (2 : ℂ) * Real.pi * Complex.I * ((((j₁ : ℝ) / d - (j₂ : ℝ) / d : ℝ) : ℂ))
        = (2 : ℂ) * Real.pi * Complex.I * (m : ℂ) := by rw [hm]; ring
    have hdivR : (j₁ : ℝ) / d - (j₂ : ℝ) / d = (m : ℝ) := by exact_mod_cast mul_left_cancel₀ hpi hmul
    have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hlt1 : (j₁ : ℝ) / d < 1 := (div_lt_one hdR).mpr (by exact_mod_cast hj₁)
    have hlt2 : (j₂ : ℝ) / d < 1 := (div_lt_one hdR).mpr (by exact_mod_cast hj₂)
    have hnn1 : (0 : ℝ) ≤ (j₁ : ℝ) / d := by positivity
    have hnn2 : (0 : ℝ) ≤ (j₂ : ℝ) / d := by positivity
    have hm0 : m = 0 := by
      have hm1 : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
      have hm2 : -1 < m := by exact_mod_cast (show (-1 : ℝ) < (m : ℝ) by linarith)
      omega
    rw [hm0, Int.cast_zero, sub_eq_zero] at hdivR
    have hR : (j₁ : ℝ) = (j₂ : ℝ) := (div_left_inj' (ne_of_gt hdR)).mp hdivR
    exact_mod_cast hR
  -- Form polynomials P = X^d - 1 and Q = ∏_{j < d} (X - C (ω j))
  let P : Polynomial ℂ := Polynomial.X ^ d - 1
  let Q : Polynomial ℂ := ∏ j ∈ Finset.range d, (Polynomial.X - Polynomial.C (ω j))
  have hQ_dvd_P : Q ∣ P := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro j₁ hj₁ j₂ hj₂ hne
      have hω_ne : ω j₁ ≠ ω j₂ := fun h => hne (hinj hj₁ hj₂ h)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hω_ne))
    · intro j hj
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
      simp [P, hroot j hj]
  have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C 1 (ne_of_gt hd)
  have hQ_monic : Q.Monic := Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)
  have hP_deg : P.natDegree = d := Polynomial.natDegree_X_pow_sub_C
  have hQ_deg : Q.natDegree = d := by
    dsimp only [Q]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
    simp
  have hPQ : P = Q := by
    obtain ⟨R, hR⟩ := hQ_dvd_P
    have hR_ne : R ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hR; exact hP_monic.ne_zero hR
    have hdeg_add : P.natDegree = Q.natDegree + R.natDegree := by
      rw [hR, Polynomial.natDegree_mul hQ_monic.ne_zero hR_ne]
    have hR_deg0 : R.natDegree = 0 := by omega
    have hR_monic : R.Monic := by
      have hlead : P.leadingCoeff = Q.leadingCoeff * R.leadingCoeff := by
        rw [hR, Polynomial.leadingCoeff_mul]
      rw [hP_monic.leadingCoeff, hQ_monic.leadingCoeff, one_mul] at hlead
      exact hlead.symm
    have hR1 : R = 1 := Polynomial.eq_one_of_monic_natDegree_zero hR_monic hR_deg0
    rw [hR, hR1, mul_one]
  have heval := congrArg (Polynomial.eval z) hPQ
  simp only [P, Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at heval
  exact heval

/-- **Theorem 4 (Exact Gauss–Eisenstein Cotangent Multiplication Identity)**:
For EVERY `0 < d` and EVERY `x : ℝ` with `Real.sin (Real.pi * (d : ℝ) * x) ≠ 0`:
`∑ j ∈ Finset.range d, cotPi (x - (j : ℝ) / d) = (d : ℝ) * cotPi ((d : ℝ) * x)`! -/
theorem eisenstein_cotangent_sum_exact {d : ℕ} (hd : 0 < d) {x : ℝ}
    (hsin : Real.sin (Real.pi * (d : ℝ) * x) ≠ 0) :
    ∑ j ∈ Finset.range d, cotPi (x - (j : ℝ) / d) = (d : ℝ) * cotPi ((d : ℝ) * x) := by
  let z₀ : ℂ := eReal x
  have hsin_d : Real.sin (Real.pi * ((d : ℝ) * x)) ≠ 0 := by rwa [← mul_assoc]
  have ⟨hzd_ne1, hcay_d⟩ := cayley_eReal_eq_neg_I_cotPi hsin_d
  have hzd_eq : z₀ ^ d = eReal ((d : ℝ) * x) := eReal_pow x d
  have hzd_sub_ne : z₀ ^ d - 1 ≠ 0 := by rw [hzd_eq]; exact sub_ne_zero.mpr hzd_ne1
  -- Every factor z₀ - e(j/d) is nonzero because their product is z₀^d - 1 ≠ 0!
  have hfac_ne : ∀ j ∈ Finset.range d, z₀ - eReal ((j : ℝ) / d) ≠ 0 := by
    intro j hj h0
    have hprod0 : ∏ k ∈ Finset.range d, (z₀ - eReal ((k : ℝ) / d)) = 0 :=
      Finset.prod_eq_zero hj h0
    rw [← complex_pow_sub_one_eq_prod_eReal hd z₀] at hprod0
    exact hzd_sub_ne hprod0
  -- Differentiate both sides of z^d - 1 = ∏_{j < d} (z - e(j/d)) at z₀!
  have hderiv1 : HasDerivAt (fun z : ℂ => z ^ d - 1) ((d : ℂ) * z₀ ^ (d - 1)) z₀ := by
    have h := (hasDerivAt_pow d z₀).sub_const (1 : ℂ)
    exact h
  have hderiv2 : HasDerivAt (fun z : ℂ => ∏ j ∈ Finset.range d, (z - eReal ((j : ℝ) / d)))
      (∑ j ∈ Finset.range d, ∏ k ∈ (Finset.range d).erase j, (z₀ - eReal ((k : ℝ) / d))) z₀ := by
    have h := HasDerivAt.finsetProd (u := Finset.range d)
      (f := fun j (z : ℂ) => z - eReal ((j : ℝ) / d))
      (f' := fun _ => (1 : ℂ)) (x := z₀)
      (fun j _ => (hasDerivAt_id z₀).sub_const (eReal ((j : ℝ) / d)))
    have hfn : (∏ i ∈ Finset.range d, fun z : ℂ => z - eReal ((i : ℝ) / d))
        = fun z : ℂ => ∏ j ∈ Finset.range d, (z - eReal ((j : ℝ) / d)) := by
      ext z; simp [Finset.prod_apply]
    simpa [hfn] using h
  have hfun_eq : (fun z : ℂ => z ^ d - 1) = (fun z : ℂ => ∏ j ∈ Finset.range d, (z - eReal ((j : ℝ) / d))) :=
    funext (complex_pow_sub_one_eq_prod_eReal hd)
  rw [hfun_eq] at hderiv1
  have hdeq : (d : ℂ) * z₀ ^ (d - 1)
      = ∑ j ∈ Finset.range d, ∏ k ∈ (Finset.range d).erase j, (z₀ - eReal ((k : ℝ) / d)) :=
    hderiv1.unique hderiv2
  -- Divide both sides by z₀^d - 1 = ∏_{k < d} (z₀ - e(k/d)) and multiply by z₀!
  have hlogderiv : (d : ℂ) * z₀ ^ d / (z₀ ^ d - 1)
      = ∑ j ∈ Finset.range d, z₀ / (z₀ - eReal ((j : ℝ) / d)) := by
    have hz_pow : z₀ * z₀ ^ (d - 1) = z₀ ^ d := by
      have hd1 : d = (d - 1) + 1 := by omega
      conv_rhs => rw [hd1, pow_succ, mul_comm]
    calc (d : ℂ) * z₀ ^ d / (z₀ ^ d - 1)
        = z₀ * ((d : ℂ) * z₀ ^ (d - 1)) / (z₀ ^ d - 1) := by rw [← hz_pow]; ring
      _ = z₀ * (∑ j ∈ Finset.range d, ∏ k ∈ (Finset.range d).erase j, (z₀ - eReal ((k : ℝ) / d)))
            / (z₀ ^ d - 1) := by rw [hdeq]
      _ = ∑ j ∈ Finset.range d,
            z₀ * (∏ k ∈ (Finset.range d).erase j, (z₀ - eReal ((k : ℝ) / d)))
              / (∏ k ∈ Finset.range d, (z₀ - eReal ((k : ℝ) / d))) := by
            rw [Finset.mul_sum, Finset.sum_div, complex_pow_sub_one_eq_prod_eReal hd z₀]
      _ = ∑ j ∈ Finset.range d, z₀ / (z₀ - eReal ((j : ℝ) / d)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            have hprod_split : ∏ k ∈ Finset.range d, (z₀ - eReal ((k : ℝ) / d))
                = (z₀ - eReal ((j : ℝ) / d)) * ∏ k ∈ (Finset.range d).erase j, (z₀ - eReal ((k : ℝ) / d)) :=
              (Finset.mul_prod_erase (Finset.range d) _ hj).symm
            have herase_ne : ∏ k ∈ (Finset.range d).erase j, (z₀ - eReal ((k : ℝ) / d)) ≠ 0 :=
              Finset.prod_ne_zero_iff.mpr fun k hk => hfac_ne k (Finset.mem_of_mem_erase hk)
            rw [hprod_split]
            field_simp [hfac_ne j hj, herase_ne]
  -- Convert 2 * (z / (z - w)) - 1 = (z/w + 1)/(z/w - 1) = -i * cotPi(x - j/d)!
  have hC : ((∑ j ∈ Finset.range d, cotPi (x - (j : ℝ) / d) : ℝ) : ℂ)
      = (((d : ℝ) * cotPi ((d : ℝ) * x) : ℝ) : ℂ) := by
    have hI_ne : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    apply mul_left_cancel₀ hI_ne
    have hRHS : -Complex.I * (((d : ℝ) * cotPi ((d : ℝ) * x) : ℝ) : ℂ)
        = 2 * ((d : ℂ) * z₀ ^ d / (z₀ ^ d - 1)) - (d : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_natCast,
        show -Complex.I * ((d : ℂ) * (cotPi ((d : ℝ) * x) : ℂ)) = (d : ℂ) * (-Complex.I * (cotPi ((d : ℝ) * x) : ℂ)) by ring,
        ← hcay_d, ← hzd_eq]
      field_simp [hzd_sub_ne]; ring
    have hLHS : -Complex.I * ((∑ j ∈ Finset.range d, cotPi (x - (j : ℝ) / d) : ℝ) : ℂ)
        = ∑ j ∈ Finset.range d, (2 * (z₀ / (z₀ - eReal ((j : ℝ) / d))) - 1) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hsin_j : Real.sin (Real.pi * (x - (j : ℝ) / d)) ≠ 0 := by
        intro h0
        -- If sin(π(x - j/d)) = 0 then eReal(x - j/d) = 1, contradicting z₀ - e(j/d) ≠ 0!
        rw [Real.sin_eq_zero_iff] at h0
        obtain ⟨k, hk⟩ := h0
        have hdiff : x - (j : ℝ) / d = (k : ℝ) := by
          have : Real.pi * (x - (j : ℝ) / d) = Real.pi * (k : ℝ) := by linarith
          exact mul_left_cancel₀ Real.pi_ne_zero this
        have he1 : eReal (x - (j : ℝ) / d) = 1 := by
          rw [hdiff]; unfold eReal
          have harg : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
            push_cast; ring
          rw [harg, Complex.exp_int_mul_two_pi_mul_I]
        have hz_eq : z₀ = eReal ((j : ℝ) / d) := by
          have hrew : x = (x - (j : ℝ) / d) + (j : ℝ) / d := by ring
          dsimp only [z₀]; rw [hrew, eReal_add, he1, one_mul]
        exact hfac_ne j hj (sub_eq_zero.mpr hz_eq)
      have ⟨_, hcay_j⟩ := cayley_eReal_eq_neg_I_cotPi hsin_j
      rw [← hcay_j]
      have hratio : eReal (x - (j : ℝ) / d) = z₀ / eReal ((j : ℝ) / d) := by
        dsimp only [z₀]
        rw [sub_eq_add_neg, eReal_add, eReal_neg, ← div_eq_mul_inv]
      rw [hratio]
      have hw_ne : eReal ((j : ℝ) / d) ≠ 0 := Complex.exp_ne_zero _
      have hzw_ne : z₀ / eReal ((j : ℝ) / d) - 1 ≠ 0 := by
        intro h
        have : z₀ / eReal ((j : ℝ) / d) = 1 := sub_eq_zero.mp h
        exact hfac_ne j hj (sub_eq_zero.mpr ((div_eq_one_iff_eq hw_ne).mp this))
      field_simp [hw_ne, hzw_ne, hfac_ne j hj]
      ring
    rw [hLHS, hRHS, hlogderiv, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  exact_mod_cast hC

end GoldbachWave37
