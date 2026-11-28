import Mathlib

/-!
# Wave 34 — Exact Ramanujan–Farey Convolution Identity, Klüyver Tail Elimination & Farey Separation

Building directly on Wave 33 (`RamanujanSingularSeriesDuality.lean`), this file proves:

1. **Exact Full-Period Ramanujan Convolution (`ramanujan_conv_period_exact`)**:
   For any `0 < Q`, any `q₁, q₂ ∣ Q`, and any `n : ℕ`:
   `∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ ((n + Q - m % Q) % Q)`
   `= if q₁ = q₂ then (Q : ℤ) * ramanujanSum q₁ n else 0`.

2. **Exact Finite-Interval Ramanujan–Farey Convolution Decomposition (`ramanujan_conv_interval_exact`)**:
   For ANY `0 < n`, ANY `Q : ℕ`, and ANY real Ramanujan-expanded functions
   `f(x) = ∑ q ∈ Finset.Icc 1 Q, α q * c_q(x)`, `g(y) = ∑ q ∈ Finset.Icc 1 Q, β q * c_q(y)`
   (which by Wave 33 Theorem 4 includes every truncated Möbius-divisor function `F_S`, every Selberg
   weight `Λ_R`, and every `PureSquare` kernel):
   `∑ x ∈ Finset.range n, f x * g (n - x)`
   `= (n : ℝ) * ∑ q ∈ Finset.Icc 1 Q, α q * β q * c_q(n) + Re(OffDiagFarey(n, Q, α, β))`,
   splitting the Goldbach convolution into the **exact singular-series diagonal** plus the **exact
   off-diagonal Farey aliasing bilinear form** over distinct primitive fractions `(q₁, a₁) ≠ (q₂, a₂)`.

3. **Exact Klüyver Bound & Unconditional Diagonal Tail Elimination (`ramanujanSum_abs_le_sum_divisors_gcd`,
   `ramanujan_diagonal_low_bound`, `ramanujan_diagonal_tail_bound`)**:
   - `|c_q(n)| ≤ ∑ d ∈ (Nat.gcd q n).divisors, d`
   - Low spectrum: `∑ q ∈ Finset.Icc 1 N, |c_q(n)| / q² ≤ 2 * ∑ d ∈ n.divisors, (1 / d)`
   - High tail (`0 < L`): `∑ q ∈ Finset.Ioc L N, |c_q(n)| / q² ≤ (2 / L) * τ(n)`
   Consequence: choosing `L = n^{1/4}` eliminates **100% of the Ramanujan Diagonal of `PureSquare`**
   unconditionally from PNT for `μ` alone (`O(n (log n)^{-2A} log log n + n^{3/4} (log n)^2 τ(n))`),
   isolating the entire remaining `PureSquare` obstruction inside the single off-diagonal Farey
   aliasing form.

4. **Exact Farey Separation Lower Bound (`farey_distinct_separation_lower_bound`)**:
   For any two distinct reduced fractions `a₁/q₁ ≠ a₂/q₂` (`0 < q₁, q₂`, `aᵢ < qᵢ`, `(aᵢ, qᵢ) = 1`)
   and EVERY `k : ℤ`:
   `1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂ - (k : ℝ)|`.

5. **Exact Selberg–Ramanujan Reflection Identity (`selberg_ramanujan_reflection_identity`)**:
   `∑ x ∈ Finset.Ico 1 n, f x * f (n - x)`
   `= 2 * ∑ x ∈ Finset.Ico 1 n, f x * g (n - x) - ∑ x ∈ Finset.Ico 1 n, g x * g (n - x)`
   `  + ∑ x ∈ Finset.Ico 1 n, (f x - g x) * (f (n - x) - g (n - x))`.
-/

open scoped BigOperators
open ArithmeticFunction

namespace GoldbachWave34

local notation "μ" => ArithmeticFunction.moebius

/-! ### Self-contained definitions (matching Wave 33) -/

/-- Exact integer Ramanujan sum `c_q(m) = ∑_{d ∣ gcd(q, m)} d * μ(q / d)`. -/
def ramanujanSum (q m : ℕ) : ℤ :=
  ∑ d ∈ (Nat.gcd q m).divisors, (d : ℤ) * μ (q / d)

/-- Additive character `e(θ) = exp(2π i θ)` for `θ : ℝ`. -/
noncomputable def eReal (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))

/-- Rational additive character `e(m / q)`. -/
noncomputable def eFrac (m : ℤ) (q : ℕ) : ℂ :=
  eReal ((m : ℝ) / (q : ℝ))

/-- Complex exponential sum definition of Ramanujan's sum:
`∑_{0 ≤ a < q, (a, q) = 1} e(a m / q)`. -/
noncomputable def ramanujanExp (q m : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), eFrac ((a : ℤ) * (m : ℤ)) q

/-- Finite geometric exponential sum `G_n(θ) = ∑_{x=0}^{n-1} e(x θ)`. -/
noncomputable def geomExpSum (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ x ∈ Finset.range n, eReal ((x : ℝ) * θ)

/-- Exact off-diagonal Farey aliasing bilinear form for Ramanujan coefficients `α, β` up to `Q`. -/
noncomputable def offDiagFareyForm (n Q : ℕ) (α β : ℕ → ℝ) : ℂ :=
  ∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q,
    ((α q₁ * β q₂ : ℝ) : ℂ) *
      ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
        ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
          if (q₁, a₁) = (q₂, a₂) then 0
          else eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)

/-! ### Private Helpers: Character Algebra & Klüyver Identity -/

private lemma eReal_add (θ₁ θ₂ : ℝ) : eReal (θ₁ + θ₂) = eReal θ₁ * eReal θ₂ := by
  unfold eReal
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

private lemma eReal_zero : eReal 0 = 1 := by
  unfold eReal; simp

private lemma eReal_int (k : ℤ) : eReal (k : ℝ) = 1 := by
  unfold eReal
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private lemma eFrac_add (m₁ m₂ : ℤ) (q : ℕ) :
    eFrac (m₁ + m₂) q = eFrac m₁ q * eFrac m₂ q := by
  unfold eFrac
  rw [← eReal_add]; congr 1; push_cast; ring

private lemma eFrac_pow (m : ℤ) (q k : ℕ) :
    (eFrac m q) ^ k = eFrac ((k : ℤ) * m) q := by
  induction k with
  | zero => simp [eFrac, eReal_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← eFrac_add]
    congr 1; push_cast; ring

private lemma eFrac_cancel_mul {c q : ℕ} (hc : 0 < c) (m : ℤ) :
    eFrac ((c : ℤ) * m) (c * q) = eFrac m q := by
  unfold eFrac
  have hcR : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hc)
  congr 1; push_cast
  field_simp [hcR]

private lemma eFrac_eq_one_iff {q : ℕ} (hq : 0 < q) (m : ℤ) :
    eFrac m q = 1 ↔ (q : ℤ) ∣ m := by
  unfold eFrac eReal
  rw [Complex.exp_eq_one_iff]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have hpi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨k, hk⟩
    have hmul : (2 : ℂ) * Real.pi * Complex.I * (((m : ℝ) / (q : ℝ) : ℝ) : ℂ)
        = (2 : ℂ) * Real.pi * Complex.I * (k : ℂ) := by
      rw [hk]; ring
    have hdivC : (((m : ℝ) / (q : ℝ) : ℝ) : ℂ) = (k : ℂ) := mul_left_cancel₀ hpi hmul
    have hdivR : (m : ℝ) / (q : ℝ) = (k : ℝ) := by exact_mod_cast hdivC
    have hmR : (m : ℝ) = (q : ℝ) * (k : ℝ) := by
      have h := (div_eq_iff hqR).mp hdivR
      linarith
    have hmZ : m = (q : ℤ) * k := by exact_mod_cast hmR
    exact ⟨k, hmZ⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
    field_simp [hqC]

private lemma eFrac_orthogonality {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ∑ j ∈ Finset.range q, eFrac ((j : ℤ) * m) q = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  have hpow : ∀ j ∈ Finset.range q, eFrac ((j : ℤ) * m) q = (eFrac m q) ^ j :=
    fun j _ => (eFrac_pow m q j).symm
  rw [Finset.sum_congr rfl hpow]
  by_cases hdvd : (q : ℤ) ∣ m
  · have h1 : eFrac m q = 1 := (eFrac_eq_one_iff hq m).mpr hdvd
    simp [hdvd, h1]
  · have hne : eFrac m q ≠ 1 := fun h => hdvd ((eFrac_eq_one_iff hq m).mp h)
    rw [if_neg hdvd, geom_sum_eq hne, eFrac_pow]
    have htop : eFrac ((q : ℤ) * m) q = 1 := (eFrac_eq_one_iff hq _).mpr (dvd_mul_right _ _)
    simp [htop]

private lemma sum_divisors_ramanujanSum {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ q ∈ d.divisors, ramanujanSum q m = if d ∣ m then (d : ℤ) else 0 := by
  unfold ramanujanSum
  have hrew : ∑ q ∈ d.divisors, ∑ g ∈ (Nat.gcd q m).divisors, (g : ℤ) * μ (q / g)
      = ∑ q ∈ d.divisors, ∑ g ∈ d.divisors, if g ∣ q ∧ g ∣ m then (g : ℤ) * μ (q / g) else 0 := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext g
    have hqd : q ∣ d := Nat.dvd_of_mem_divisors hq
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hgq, hgm⟩, _⟩
      exact ⟨⟨dvd_trans hgq hqd, ne_of_gt hd⟩, hgq, hgm⟩
    · rintro ⟨_, hgq, hgm⟩
      exact ⟨⟨hgq, hgm⟩, ne_of_gt (Nat.gcd_pos_of_pos_left m (Nat.pos_of_dvd_of_pos hqd hd))⟩
  rw [hrew, Finset.sum_comm]
  have hinner : ∀ g ∈ d.divisors,
      (∑ q ∈ d.divisors, if g ∣ q ∧ g ∣ m then (g : ℤ) * μ (q / g) else 0)
        = if g = d ∧ d ∣ m then (d : ℤ) else 0 := by
    intro g hg
    have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
    have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgd hd
    by_cases hgm : g ∣ m
    · simp only [hgm, and_true]
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      have hbij : ∑ q ∈ d.divisors.filter (fun q => g ∣ q), μ (q / g)
          = ∑ t ∈ (d / g).divisors, μ t := by
        refine Finset.sum_bij (fun q _ => q / g) ?_ ?_ ?_ ?_
        · intro q hq
          rw [Finset.mem_filter, Nat.mem_divisors] at hq
          rw [Nat.mem_divisors]
          exact ⟨Nat.div_dvd_div hq.2 hq.1.1, ne_of_gt (Nat.div_pos (Nat.le_of_dvd hd hgd) hg_pos)⟩
        · intro q₁ hq₁ q₂ hq₂ heq
          rw [Finset.mem_filter] at hq₁ hq₂
          calc q₁ = g * (q₁ / g) := (Nat.mul_div_cancel' hq₁.2).symm
            _ = g * (q₂ / g) := by rw [heq]
            _ = q₂ := Nat.mul_div_cancel' hq₂.2
        · intro t ht
          rw [Nat.mem_divisors] at ht
          refine ⟨g * t, ?_, Nat.mul_div_cancel_left t hg_pos⟩
          rw [Finset.mem_filter, Nat.mem_divisors]
          refine ⟨⟨?_, ne_of_gt hd⟩, dvd_mul_right g t⟩
          calc g * t ∣ g * (d / g) := Nat.mul_dvd_mul_left g ht.1
            _ = d := Nat.mul_div_cancel' hgd
        · intro _ _; rfl
      rw [hbij]
      have hmu_sum : ∑ t ∈ (d / g).divisors, μ t = if d / g = 1 then (1 : ℤ) else 0 := by
        have h := ArithmeticFunction.moebius_mul_coe_zeta
        have hv := congrArg (fun f : ArithmeticFunction ℤ => f (d / g)) h
        simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply,
          ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply] at hv
        have hnat : ∑ x ∈ (d / g).divisorsAntidiagonal, μ x.1 * ((if x.2 = 0 then 0 else 1 : ℕ) : ℤ)
            = ∑ t ∈ (d / g).divisors, μ t := by
          rw [Nat.sum_divisorsAntidiagonal (f := fun a b => μ a * ((if b = 0 then 0 else 1 : ℕ) : ℤ))]
          refine Finset.sum_congr rfl fun t ht => ?_
          have hdg_pos : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg_pos
          have ht_le : t ≤ d / g := Nat.le_of_dvd hdg_pos (Nat.dvd_of_mem_divisors ht)
          have hdiv_pos : 0 < (d / g) / t := Nat.div_pos ht_le (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors ht) hdg_pos)
          simp [ne_of_gt hdiv_pos]
        rw [← hnat, hv]
      rw [hmu_sum]
      have hdg1 : d / g = 1 ↔ g = d := by
        constructor
        · intro h1; calc g = g * (d / g) := by rw [h1, mul_one]
            _ = d := Nat.mul_div_cancel' hgd
        · rintro rfl; exact Nat.div_self hd
      by_cases hgd_eq : g = d
      · subst hgd_eq; simp [hdg1.mpr rfl, hgm]
      · simp [hdg1, hgd_eq]
    · have hne : ¬(g = d ∧ d ∣ m) := by rintro ⟨rfl, h⟩; exact hgm h
      simp [hgm, hne]
  rw [Finset.sum_congr rfl hinner]
  by_cases hdm : d ∣ m
  · rw [if_pos hdm, Finset.sum_eq_single d]
    · simp [hdm]
    · intro g _ hne; simp [hne]
    · intro hnot; exact absurd (Nat.mem_divisors.mpr ⟨dvd_refl d, ne_of_gt hd⟩) hnot
  · simp [hdm]

private lemma sum_divisors_ramanujanExp {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ q ∈ d.divisors, ramanujanExp q m = if d ∣ m then (d : ℂ) else 0 := by
  have hpart : ∑ j ∈ Finset.range d, eFrac ((j : ℤ) * (m : ℤ)) d
      = ∑ q ∈ d.divisors, ramanujanExp q m := by
    have hsig : ∑ q ∈ d.divisors, ramanujanExp q m
        = ∑ p ∈ d.divisors.sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)),
            eFrac ((p.2 : ℤ) * (m : ℤ)) p.1 :=
      Finset.sum_sigma' d.divisors (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
        (fun q a => eFrac ((a : ℤ) * (m : ℤ)) q)
    rw [hsig]
    refine Finset.sum_bij (fun j _ => ⟨d / Nat.gcd j d, j / Nat.gcd j d⟩) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      have hg_pos : 0 < Nat.gcd j d := Nat.gcd_pos_of_pos_right j hd
      have hgd : Nat.gcd j d ∣ d := Nat.gcd_dvd_right j d
      rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.div_dvd_of_dvd hgd, ne_of_gt hd⟩, ?_, Nat.coprime_div_gcd_div_gcd hg_pos⟩
      have hmul : Nat.gcd j d * (j / Nat.gcd j d) < Nat.gcd j d * (d / Nat.gcd j d) := by
        rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left j d), Nat.mul_div_cancel' hgd]; exact hj
      exact Nat.lt_of_mul_lt_mul_left hmul
    · intro j₁ _ j₂ _ heq
      have h1 : d / Nat.gcd j₁ d = d / Nat.gcd j₂ d := congrArg Sigma.fst heq
      have h2 : j₁ / Nat.gcd j₁ d = j₂ / Nat.gcd j₂ d := by simpa using congrArg Sigma.snd heq
      have hg1_pos : 0 < Nat.gcd j₁ d := Nat.gcd_pos_of_pos_right j₁ hd
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
      have hgcd : Nat.gcd (g * a) d = g := by rw [← hqg, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
      ext <;> dsimp only
      · rw [hgcd, ← hqg, Nat.mul_div_cancel_left q hg_pos]
      · rw [hgcd, Nat.mul_div_cancel_left a hg_pos]
    · intro j _
      let c := Nat.gcd j d
      have hc_pos : 0 < c := Nat.gcd_pos_of_pos_right j hd
      have hcj : c * (j / c) = j := Nat.mul_div_cancel' (Nat.gcd_dvd_left j d)
      have hcd : c * (d / c) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right j d)
      conv_lhs => rw [← hcj, ← hcd]
      have hrew : ((c * (j / c) : ℕ) : ℤ) * (m : ℤ) = (c : ℤ) * (((j / c : ℕ) : ℤ) * (m : ℤ)) := by
        push_cast; ring
      rw [hrew, eFrac_cancel_mul hc_pos]
  rw [← hpart, eFrac_orthogonality hd]
  have hdvd : (d : ℤ) ∣ (m : ℤ) ↔ d ∣ m := Int.natCast_dvd_natCast
  simp [hdvd]

private lemma ramanujanSum_eq_exp {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ramanujanExp q m = (ramanujanSum q m : ℂ) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    have h1 := sum_divisors_ramanujanExp hq m
    have h2 : ∑ d ∈ q.divisors, (ramanujanSum d m : ℂ) = if q ∣ m then (q : ℂ) else 0 := by
      have hZ := sum_divisors_ramanujanSum hq m
      have hC := congrArg (fun z : ℤ => (z : ℂ)) hZ
      simpa using hC
    have hsplit1 : ∑ d ∈ q.divisors, ramanujanExp d m
        = ramanujanExp q m + ∑ d ∈ q.properDivisors, ramanujanExp d m := by
      rw [← Nat.cons_self_properDivisors (ne_of_gt hq), Finset.sum_cons]
    have hsplit2 : ∑ d ∈ q.divisors, (ramanujanSum d m : ℂ)
        = (ramanujanSum q m : ℂ) + ∑ d ∈ q.properDivisors, (ramanujanSum d m : ℂ) := by
      rw [← Nat.cons_self_properDivisors (ne_of_gt hq), Finset.sum_cons]
    have hprop_eq : ∑ d ∈ q.properDivisors, ramanujanExp d m
        = ∑ d ∈ q.properDivisors, (ramanujanSum d m : ℂ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := Nat.mem_properDivisors.mp hd
      exact ih d hd'.2 (Nat.pos_of_dvd_of_pos hd'.1 hq)
    rw [hsplit1] at h1
    rw [hsplit2, ← hprop_eq] at h2
    linear_combination h1 - h2

/-- Periodicity of `ramanujanSum q` modulo `q`: if `m₁ ≡ m₂ [MOD q]`, then `c_q(m₁) = c_q(m₂)`. -/
private lemma ramanujanSum_modEq {q m₁ m₂ : ℕ} (h : m₁ ≡ m₂ [MOD q]) :
    ramanujanSum q m₁ = ramanujanSum q m₂ := by
  unfold ramanujanSum
  have hg : Nat.gcd q m₁ = Nat.gcd q m₂ := by
    rw [Nat.gcd_comm q m₁, Nat.gcd_comm q m₂]
    exact h.gcd_eq
  rw [hg]

/-- Reduced-fraction uniqueness: if `0 < q₁, q₂`, `aᵢ < qᵢ`, `(aᵢ, qᵢ) = 1`, and `a₁ * q₂ = a₂ * q₁`,
then `q₁ = q₂ ∧ a₁ = a₂`. -/
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

/-! ### Theorem 1: Exact Full-Period Ramanujan Convolution on `ℤ / Qℤ` -/

/-- **Theorem 1 (Exact Full-Period Ramanujan Convolution Identity on `ℤ / Qℤ`)**:
For any `0 < Q`, any `q₁, q₂ ∣ Q`, and any `n : ℕ`:
`∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ ((n + Q - m % Q) % Q)`
`= if q₁ = q₂ then (Q : ℤ) * ramanujanSum q₁ n else 0`!
Notice how the diagonal `q₁ = q₂` produces `Q * c_{q₁}(n)` directly — the exact Ramanujan
singular-series kernel! -/
theorem ramanujan_conv_period_exact {Q q₁ q₂ : ℕ} (hQ : 0 < Q) (hq₁ : q₁ ∣ Q) (hq₂ : q₂ ∣ Q)
    (n : ℕ) :
    ∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ ((n + Q - m % Q) % Q)
      = if q₁ = q₂ then (Q : ℤ) * ramanujanSum q₁ n else 0 := by
  have hq1_pos : 0 < q₁ := Nat.pos_of_dvd_of_pos hq₁ hQ
  have hq2_pos : 0 < q₂ := Nat.pos_of_dvd_of_pos hq₂ hQ
  let c₁ := Q / q₁
  let c₂ := Q / q₂
  have hc1_pos : 0 < c₁ := Nat.div_pos (Nat.le_of_dvd hQ hq₁) hq1_pos
  have hc2_pos : 0 < c₂ := Nat.div_pos (Nat.le_of_dvd hQ hq₂) hq2_pos
  have hc1_eq : c₁ * q₁ = Q := by rw [mul_comm]; exact Nat.mul_div_cancel' hq₁
  have hc2_eq : c₂ * q₂ = Q := by rw [mul_comm]; exact Nat.mul_div_cancel' hq₂
  have hC : ((∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ ((n + Q - m % Q) % Q) : ℤ) : ℂ)
      = ((if q₁ = q₂ then (Q : ℤ) * ramanujanSum q₁ n else 0 : ℤ) : ℂ) := by
    have hL : ((∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ ((n + Q - m % Q) % Q) : ℤ) : ℂ)
        = ∑ m ∈ Finset.range Q, ramanujanExp q₁ m * ramanujanExp q₂ ((n + Q - m % Q) % Q) := by
      push_cast
      refine Finset.sum_congr rfl fun m _ => by
        rw [ramanujanSum_eq_exp hq1_pos, ramanujanSum_eq_exp hq2_pos]
    rw [hL]
    -- For m < Q, eFrac (a₂ * ((n + Q - m%Q) % Q)) q₂ = eFrac (a₂ * n) q₂ * eFrac (-(a₂ * m)) q₂
    have he_shift : ∀ m ∈ Finset.range Q, ∀ a₂ : ℕ,
        eFrac ((a₂ : ℤ) * (((n + Q - m % Q) % Q : ℕ) : ℤ)) q₂
          = eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * eFrac (-((a₂ : ℤ) * (m : ℤ))) q₂ := by
      intro m hm a₂
      have hm_lt : m < Q := Finset.mem_range.mp hm
      have hmod : m % Q = m := Nat.mod_eq_of_lt hm_lt
      rw [hmod, ← eFrac_add]
      have hsub : (n + Q - m) % Q + Q * ((n + Q - m) / Q) = n + Q - m :=
        Nat.mod_add_div (n + Q - m) Q
      have hZ : (((n + Q - m) % Q : ℕ) : ℤ) - ((n : ℤ) - (m : ℤ))
          = (Q : ℤ) * (1 - (((n + Q - m) / Q : ℕ) : ℤ)) := by
        have h1 : (((n + Q - m) % Q : ℕ) : ℤ) + (Q : ℤ) * (((n + Q - m) / Q : ℕ) : ℤ)
            = (n : ℤ) + (Q : ℤ) - (m : ℤ) := by
          have : ((n + Q - m : ℕ) : ℤ) = (n : ℤ) + (Q : ℤ) - (m : ℤ) := by omega
          rw [← this]; exact_mod_cast hsub
        linarith
      have hdiff : (a₂ : ℤ) * (((n + Q - m) % Q : ℕ) : ℤ)
          = ((a₂ : ℤ) * (n : ℤ) + -((a₂ : ℤ) * (m : ℤ)))
            + (q₂ : ℤ) * ((c₂ : ℤ) * (a₂ : ℤ) * (1 - (((n + Q - m) / Q : ℕ) : ℤ))) := by
        have hQ2 : (Q : ℤ) = (c₂ : ℤ) * (q₂ : ℤ) := by exact_mod_cast hc2_eq.symm
        linear_combination (a₂ : ℤ) * hZ + (a₂ : ℤ) * (1 - (((n + Q - m) / Q : ℕ) : ℤ)) * hQ2
      rw [hdiff, eFrac_add]
      have h1 : eFrac ((q₂ : ℤ) * ((c₂ : ℤ) * (a₂ : ℤ) * (1 - (((n + Q - m) / Q : ℕ) : ℤ)))) q₂ = 1 :=
        (eFrac_eq_one_iff hq2_pos _).mpr (dvd_mul_right _ _)
      rw [h1, mul_one]
    have hexp : ∑ m ∈ Finset.range Q, ramanujanExp q₁ m * ramanujanExp q₂ ((n + Q - m % Q) % Q)
        = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ *
              ∑ m ∈ Finset.range Q, eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ))) Q := by
      calc ∑ m ∈ Finset.range Q, ramanujanExp q₁ m * ramanujanExp q₂ ((n + Q - m % Q) % Q)
          = ∑ m ∈ Finset.range Q,
              ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ *
                  eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ))) Q := by
              refine Finset.sum_congr rfl fun m hm => ?_
              unfold ramanujanExp
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a₁ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a₂ _ => ?_
              rw [he_shift m hm a₂]
              have he1 : eFrac ((a₁ : ℤ) * (m : ℤ)) q₁ = eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ))) Q := by
                rw [← hc1_eq, ← eFrac_cancel_mul hc1_pos]; congr 1; ring
              have he2 : eFrac (-((a₂ : ℤ) * (m : ℤ))) q₂ = eFrac ((m : ℤ) * (-((c₂ : ℤ) * (a₂ : ℤ)))) Q := by
                rw [← hc2_eq, ← eFrac_cancel_mul hc2_pos]; congr 1; ring
              rw [he1, he2, ← mul_assoc, mul_comm (eFrac _ Q) (eFrac ((a₂ : ℤ) * (n : ℤ)) q₂),
                mul_assoc, ← eFrac_add]
              congr 2; ring
        _ = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ m ∈ Finset.range Q,
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
              eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ *
                eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ))) Q := Finset.sum_comm
        _ = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            ∑ m ∈ Finset.range Q,
              eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ *
                eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ))) Q :=
            Finset.sum_congr rfl fun a₁ _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => (Finset.mul_sum _ _ _).symm
    rw [hexp]
    have hinner : ∀ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
        ∀ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
          (∑ m ∈ Finset.range Q, eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ))) Q)
            = if q₁ = q₂ ∧ a₁ = a₂ then (Q : ℂ) else 0 := by
      intro a₁ ha₁ a₂ ha₂
      rw [eFrac_orthogonality hQ]
      have ha1' := Finset.mem_filter.mp ha₁
      have ha2' := Finset.mem_filter.mp ha₂
      have ha1_lt : a₁ < q₁ := Finset.mem_range.mp ha1'.1
      have ha2_lt : a₂ < q₂ := Finset.mem_range.mp ha2'.1
      have hiff : (Q : ℤ) ∣ ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ)) ↔ q₁ = q₂ ∧ a₁ = a₂ := by
        constructor
        · intro hdvd
          have hlt1 : (c₁ : ℤ) * (a₁ : ℤ) < (Q : ℤ) := by
            have : c₁ * a₁ < c₁ * q₁ := Nat.mul_lt_mul_of_pos_left ha1_lt hc1_pos
            rw [hc1_eq] at this; exact_mod_cast this
          have hlt2 : (c₂ : ℤ) * (a₂ : ℤ) < (Q : ℤ) := by
            have : c₂ * a₂ < c₂ * q₂ := Nat.mul_lt_mul_of_pos_left ha2_lt hc2_pos
            rw [hc2_eq] at this; exact_mod_cast this
          have h0 : (c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ) = 0 := by
            obtain ⟨t, ht⟩ := hdvd
            have h1 : -((Q : ℤ)) < (Q : ℤ) * t := by nlinarith
            have h2 : (Q : ℤ) * t < (Q : ℤ) := by nlinarith
            have ht0 : t = 0 := by nlinarith
            rw [ht0, mul_zero] at ht; exact ht
          have heqZ : (c₁ : ℤ) * (a₁ : ℤ) = (c₂ : ℤ) * (a₂ : ℤ) := by linarith
          have heqN : c₁ * a₁ = c₂ * a₂ := by exact_mod_cast heqZ
          have hmul : Q * (a₁ * q₂) = Q * (a₂ * q₁) := by
            calc Q * (a₁ * q₂) = (c₁ * a₁) * (q₁ * q₂) := by rw [← hc1_eq]; ring
              _ = (c₂ * a₂) * (q₁ * q₂) := by rw [heqN]
              _ = Q * (a₂ * q₁) := by rw [← hc2_eq]; ring
          exact (coprime_frac_eq_iff hq1_pos hq2_pos ha1'.2 ha2'.2).mp
            (Nat.eq_of_mul_eq_mul_left hQ hmul)
        · rintro ⟨rfl, rfl⟩
          have hc : c₁ = c₂ := rfl
          rw [hc, sub_self]; exact dvd_zero _
      simp [hiff]
    have hsum2 : ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ *
              ∑ m ∈ Finset.range Q, eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) - (c₂ : ℤ) * (a₂ : ℤ))) Q
        = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * (if q₁ = q₂ ∧ a₁ = a₂ then (Q : ℂ) else 0) :=
      Finset.sum_congr rfl fun a₁ ha₁ => Finset.sum_congr rfl fun a₂ ha₂ => by rw [hinner a₁ ha₁ a₂ ha₂]
    rw [hsum2]
    by_cases hqeq : q₁ = q₂
    · subst hqeq
      simp only [true_and, ↓reduceIte, Int.cast_mul, Int.cast_natCast]
      have hdiag : ∀ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          (∑ a₂ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            eFrac ((a₂ : ℤ) * (n : ℤ)) q₁ * (if a₁ = a₂ then (Q : ℂ) else 0))
            = (Q : ℂ) * eFrac ((a₁ : ℤ) * (n : ℤ)) q₁ := by
        intro a₁ ha₁
        rw [Finset.sum_eq_single a₁]
        · simp [mul_comm]
        · intro a₂ _ hne; simp [hne.symm]
        · intro hnot; exact absurd ha₁ hnot
      rw [Finset.sum_congr rfl hdiag, ← Finset.mul_sum]
      change (Q : ℂ) * ramanujanExp q₁ n = (Q : ℂ) * (ramanujanSum q₁ n : ℂ)
      rw [ramanujanSum_eq_exp hq1_pos]
    · simp [hqeq]
  exact_mod_cast hC

/-! ### Theorem 2: Exact Finite-Interval Ramanujan–Farey Convolution Decomposition -/

/-- **Theorem 2 (Exact Finite-Interval Ramanujan–Farey Convolution Decomposition)**:
For ANY `n Q : ℕ` and ANY real Ramanujan-expanded functions
`f(x) = ∑ q ∈ Finset.Icc 1 Q, α q * c_q(x)`, `g(y) = ∑ q ∈ Finset.Icc 1 Q, β q * c_q(y)`:
`((∑ x ∈ Finset.range n, f x * g (n - x) : ℝ) : ℂ)`
`= (n : ℂ) * ∑ q ∈ Finset.Icc 1 Q, ((α q * β q : ℝ) : ℂ) * (ramanujanSum q n : ℂ) + offDiagFareyForm n Q α β`!
In particular, taking real parts gives the exact real-valued singular-series + Farey-aliasing split! -/
theorem ramanujan_conv_interval_exact (n Q : ℕ) (α β : ℕ → ℝ) :
    ((∑ x ∈ Finset.range n,
        (∑ q ∈ Finset.Icc 1 Q, α q * (ramanujanSum q x : ℝ)) *
        (∑ q ∈ Finset.Icc 1 Q, β q * (ramanujanSum q (n - x) : ℝ)) : ℝ) : ℂ)
      = (n : ℂ) * (∑ q ∈ Finset.Icc 1 Q, ((α q * β q : ℝ) : ℂ) * (ramanujanSum q n : ℂ))
        + offDiagFareyForm n Q α β := by
  -- Expand LHS into ∑_{q₁, q₂} α q₁ β q₂ ∑_{x < n} c_{q₁}(x) c_{q₂}(n - x)
  have hexpand : ((∑ x ∈ Finset.range n,
        (∑ q ∈ Finset.Icc 1 Q, α q * (ramanujanSum q x : ℝ)) *
        (∑ q ∈ Finset.Icc 1 Q, β q * (ramanujanSum q (n - x) : ℝ)) : ℝ) : ℂ)
      = ∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q,
          ((α q₁ * β q₂ : ℝ) : ℂ) *
            ∑ x ∈ Finset.range n, ramanujanExp q₁ x * ramanujanExp q₂ (n - x) := by
    rw [Complex.ofReal_sum]
    calc ∑ x ∈ Finset.range n,
          (((∑ q ∈ Finset.Icc 1 Q, α q * (ramanujanSum q x : ℝ)) *
            (∑ q ∈ Finset.Icc 1 Q, β q * (ramanujanSum q (n - x) : ℝ)) : ℝ) : ℂ)
        = ∑ x ∈ Finset.range n,
            ∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q,
              ((α q₁ * β q₂ : ℝ) : ℂ) * (ramanujanExp q₁ x * ramanujanExp q₂ (n - x)) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q₂ hq₂ => ?_
            have hq1_pos : 0 < q₁ := (Finset.mem_Icc.mp hq₁).1
            have hq2_pos : 0 < q₂ := (Finset.mem_Icc.mp hq₂).1
            rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_intCast,
              ← ramanujanSum_eq_exp hq1_pos, ← ramanujanSum_eq_exp hq2_pos, Complex.ofReal_mul]
            ring
      _ = ∑ q₁ ∈ Finset.Icc 1 Q, ∑ x ∈ Finset.range n, ∑ q₂ ∈ Finset.Icc 1 Q,
            ((α q₁ * β q₂ : ℝ) : ℂ) * (ramanujanExp q₁ x * ramanujanExp q₂ (n - x)) := Finset.sum_comm
      _ = ∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q, ∑ x ∈ Finset.range n,
            ((α q₁ * β q₂ : ℝ) : ℂ) * (ramanujanExp q₁ x * ramanujanExp q₂ (n - x)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
  rw [hexpand]
  -- For each pair (q₁, q₂), decompose ∑_{x < n} ramanujanExp q₁ x * ramanujanExp q₂ (n - x)
  have hpair : ∀ q₁ ∈ Finset.Icc 1 Q, ∀ q₂ ∈ Finset.Icc 1 Q,
      ∑ x ∈ Finset.range n, ramanujanExp q₁ x * ramanujanExp q₂ (n - x)
        = (if q₁ = q₂ then (n : ℂ) * (ramanujanSum q₁ n : ℂ) else 0)
          + ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                if (q₁, a₁) = (q₂, a₂) then 0
                else eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂) := by
    intro q₁ hq₁ q₂ hq₂
    have hq1_pos : 0 < q₁ := (Finset.mem_Icc.mp hq₁).1
    have hq2_pos : 0 < q₂ := (Finset.mem_Icc.mp hq₂).1
    have hinner : ∑ x ∈ Finset.range n, ramanujanExp q₁ x * ramanujanExp q₂ (n - x)
        = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
              eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂) := by
      calc ∑ x ∈ Finset.range n, ramanujanExp q₁ x * ramanujanExp q₂ (n - x)
          = ∑ x ∈ Finset.range n,
              ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * eReal ((x : ℝ) * ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              have hx_lt : x < n := Finset.mem_range.mp hx
              unfold ramanujanExp
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a₁ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a₂ _ => ?_
              unfold eFrac
              rw [← eReal_add, ← eReal_add]
              congr 1
              have hsub : ((n - x : ℕ) : ℝ) = (n : ℝ) - (x : ℝ) := Nat.cast_sub (le_of_lt hx_lt)
              push_cast; rw [hsub]; ring
        _ = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ x ∈ Finset.range n,
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
              eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * eReal ((x : ℝ) * ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)) := Finset.sum_comm
        _ = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            ∑ x ∈ Finset.range n,
              eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * eReal ((x : ℝ) * ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
            rw [← Finset.mul_sum]; rfl
    rw [hinner]
    -- Split the (a₁, a₂) sum into (q₁, a₁) = (q₂, a₂) and (q₁, a₁) ≠ (q₂, a₂)!
    have hsplit : ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)
        = (∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
              if (q₁, a₁) = (q₂, a₂) then
                eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)
              else 0)
          + (∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                if (q₁, a₁) = (q₂, a₂) then 0
                else eFrac ((a₂ : ℤ) * (n : ℤ)) q₂ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      split_ifs <;> simp
    rw [hsplit]
    congr 1
    by_cases hqeq : q₁ = q₂
    · subst hqeq
      rw [if_pos rfl]
      have hdiag : ∀ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          (∑ a₂ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            if (q₁, a₁) = (q₁, a₂) then
              eFrac ((a₂ : ℤ) * (n : ℤ)) q₁ * geomExpSum n ((a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₁)
            else 0) = (n : ℂ) * eFrac ((a₁ : ℤ) * (n : ℤ)) q₁ := by
        intro a₁ ha₁
        rw [Finset.sum_eq_single a₁]
        · simp only [↓reduceIte, sub_self]
          have hg0 : geomExpSum n 0 = (n : ℂ) := by
            unfold geomExpSum; simp [eReal_zero]
          rw [hg0, mul_comm]
        · intro a₂ _ hne
          have hpair_ne : (q₁, a₁) ≠ (q₁, a₂) := fun h => hne (Prod.mk.inj h).2.symm
          simp [hpair_ne]
        · intro hnot; exact absurd ha₁ hnot
      rw [Finset.sum_congr rfl hdiag, ← Finset.mul_sum]
      change (n : ℂ) * ramanujanExp q₁ n = (n : ℂ) * (ramanujanSum q₁ n : ℂ)
      rw [ramanujanSum_eq_exp hq1_pos]
    · rw [if_neg hqeq]
      refine Finset.sum_eq_zero fun a₁ _ => Finset.sum_eq_zero fun a₂ _ => ?_
      have hne : (q₁, a₁) ≠ (q₂, a₂) := fun h => hqeq (Prod.mk.inj h).1
      simp [hne]
  -- Assemble over q₁, q₂ ∈ Icc 1 Q
  have hsum : ∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q,
        ((α q₁ * β q₂ : ℝ) : ℂ) * ∑ x ∈ Finset.range n, ramanujanExp q₁ x * ramanujanExp q₂ (n - x)
      = (∑ q₁ ∈ Finset.Icc 1 Q, ∑ q₂ ∈ Finset.Icc 1 Q,
          ((α q₁ * β q₂ : ℝ) : ℂ) * (if q₁ = q₂ then (n : ℂ) * (ramanujanSum q₁ n : ℂ) else 0))
        + offDiagFareyForm n Q α β := by
    unfold offDiagFareyForm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q₂ hq₂ => ?_
    rw [hpair q₁ hq₁ q₂ hq₂, mul_add]
  rw [hsum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
  rw [Finset.sum_eq_single q₁]
  · simp; ring
  · intro q₂ _ hne; simp [hne.symm]
  · intro hnot; exact absurd hq₁ hnot

/-! ### Theorems 3–5: Klüyver Bound & Unconditional Diagonal Tail Elimination -/

/-- **Theorem 3 (Exact Klüyver Magnitude Bound for Ramanujan Sums)**:
For every `q, n : ℕ`, `|(ramanujanSum q n : ℝ)| ≤ ∑ d ∈ (Nat.gcd q n).divisors, (d : ℝ)`. -/
theorem ramanujanSum_abs_le_sum_divisors_gcd (q n : ℕ) :
    |(ramanujanSum q n : ℝ)| ≤ ∑ d ∈ (Nat.gcd q n).divisors, (d : ℝ) := by
  unfold ramanujanSum
  push_cast
  calc |∑ d ∈ (Nat.gcd q n).divisors, (d : ℝ) * (μ (q / d) : ℝ)|
      ≤ ∑ d ∈ (Nat.gcd q n).divisors, |(d : ℝ) * (μ (q / d) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Nat.gcd q n).divisors, (d : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
        have hmu : |(μ (q / d) : ℝ)| ≤ 1 := by
          by_cases hsf : Squarefree (q / d)
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
            push_cast; simp [abs_pow]
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
        nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- Exact elementary telescoping bound for inverse-square sums on `Ioc m M`. -/
private lemma sum_inv_sq_Ioc_le_sub {m M : ℕ} (hm : 0 < m) (hM : m ≤ M) :
    ∑ k ∈ Finset.Ioc m M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hle ih =>
    have hM_pos : 0 < M := lt_of_lt_of_le hm hle
    have hIoc : Finset.Ioc m (M + 1) = insert (M + 1) (Finset.Ioc m M) := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    have hnot : M + 1 ∉ Finset.Ioc m M := by simp
    rw [hIoc, Finset.sum_insert hnot]
    have hstep : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
      have hMR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
      have hM1R : (0 : ℝ) < (M : ℝ) + 1 := by linarith
      push_cast
      rw [div_sub_div _ _ (ne_of_gt hMR) (ne_of_gt hM1R)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private lemma sum_inv_sq_Ioc_le (m M : ℕ) :
    ∑ k ∈ Finset.Ioc m M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ if m = 0 then 2 else 1 / (m : ℝ) := by
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_pos rfl]
    by_cases hM0 : M = 0
    · subst hM0; norm_num
    · have hM1 : 1 ≤ M := Nat.pos_of_ne_zero hM0
      have hIoc : Finset.Ioc 0 M = insert 1 (Finset.Ioc 1 M) := by
        ext k; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot : (1 : ℕ) ∉ Finset.Ioc 1 M := by simp
      rw [hIoc, Finset.sum_insert hnot]
      have htail := sum_inv_sq_Ioc_le_sub (by norm_num : 0 < 1) hM1
      have hM_nonneg : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
      norm_num at htail ⊢
      linarith
  · rw [if_neg hm0]
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    by_cases hle : m ≤ M
    · have h := sum_inv_sq_Ioc_le_sub hm_pos hle
      have hM_nonneg : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
      linarith
    · have hemp : Finset.Ioc m M = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]; positivity

/-- Exact divisor-swap + `q = d * k` factorization of `∑_{q ∈ Ioc L N} |c_q(n)| / q²`. -/
private lemma ramanujan_inv_sq_Ioc_le_divisor_sum {n : ℕ} (hn : 0 < n) (L N : ℕ) :
    ∑ q ∈ Finset.Ioc L N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2
      ≤ ∑ d ∈ n.divisors, (1 / (d : ℝ)) *
          ∑ k ∈ Finset.Ioc (L / d) (N / d), (1 : ℝ) / (k : ℝ) ^ 2 := by
  calc ∑ q ∈ Finset.Ioc L N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2
      ≤ ∑ q ∈ Finset.Ioc L N, (∑ d ∈ (Nat.gcd q n).divisors, (d : ℝ)) / (q : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun q _ => div_le_div_of_nonneg_right
          (ramanujanSum_abs_le_sum_divisors_gcd q n) (sq_nonneg _)
    _ = ∑ q ∈ Finset.Ioc L N,
          ∑ d ∈ n.divisors, if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq_pos : 0 < q := lt_of_le_of_lt (Nat.zero_le L) (Finset.mem_Ioc.mp hq).1
        rw [Finset.sum_div, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
        constructor
        · rintro ⟨⟨hdq, hdn⟩, _⟩; exact ⟨⟨hdn, ne_of_gt hn⟩, hdq⟩
        · rintro ⟨⟨hdn, _⟩, hdq⟩
          exact ⟨⟨hdq, hdn⟩, ne_of_gt (Nat.gcd_pos_of_pos_left n hq_pos)⟩
    _ = ∑ d ∈ n.divisors, ∑ q ∈ Finset.Ioc L N, if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0 :=
        Finset.sum_comm
    _ = ∑ d ∈ n.divisors, (1 / (d : ℝ)) *
          ∑ k ∈ Finset.Ioc (L / d) (N / d), (1 : ℝ) / (k : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
        have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd_pos)
        rw [← Finset.sum_filter, Finset.mul_sum]
        symm
        refine Finset.sum_bij (fun k _ => d * k) ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_Ioc] at hk
          rw [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
          · rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hd_pos).mp hk.1
          · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd_pos).mp hk.2
        · intro k₁ _ k₂ _ heq; exact Nat.eq_of_mul_eq_mul_left hd_pos heq
        · intro q hq
          rw [Finset.mem_filter, Finset.mem_Ioc] at hq
          refine ⟨q / d, ?_, Nat.mul_div_cancel' hq.2⟩
          rw [Finset.mem_Ioc]
          refine ⟨(Nat.div_lt_iff_lt_mul hd_pos).mpr ?_, (Nat.le_div_iff_mul_le hd_pos).mpr ?_⟩
          · rw [mul_comm, Nat.mul_div_cancel' hq.2]; exact hq.1.1
          · rw [mul_comm, Nat.mul_div_cancel' hq.2]; exact hq.1.2
        · intro k _
          push_cast
          field_simp [hdR]

/-- **Theorem 4 (Exact Low-Spectrum Ramanujan Diagonal Bound — `O(log log n)`)**:
For every `0 < n` and every `N : ℕ`:
`∑ q ∈ Finset.Icc 1 N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2 ≤ 2 * ∑ d ∈ n.divisors, (1 / (d : ℝ))`! -/
theorem ramanujan_diagonal_low_bound {n : ℕ} (hn : 0 < n) (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2
      ≤ 2 * ∑ d ∈ n.divisors, (1 / (d : ℝ)) := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by ext q; simp; omega
  rw [hIcc]
  calc ∑ q ∈ Finset.Ioc 0 N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2
      ≤ ∑ d ∈ n.divisors, (1 / (d : ℝ)) *
          ∑ k ∈ Finset.Ioc (0 / d) (N / d), (1 : ℝ) / (k : ℝ) ^ 2 :=
        ramanujan_inv_sq_Ioc_le_divisor_sum hn 0 N
    _ ≤ ∑ d ∈ n.divisors, (1 / (d : ℝ)) * 2 := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [Nat.zero_div]
        have h := sum_inv_sq_Ioc_le 0 (N / d)
        simp only [↓reduceIte] at h
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * ∑ d ∈ n.divisors, (1 / (d : ℝ)) := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

/-- **Theorem 5 (Exact High-Tail Ramanujan Diagonal Elimination Bound — Constant `2`)**:
For EVERY `0 < n`, EVERY `0 < L`, and EVERY `N : ℕ`:
`∑ q ∈ Finset.Ioc L N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2 ≤ (2 / (L : ℝ)) * (n.divisors.card : ℝ)`!
Choosing `L = n^{1/4}` unconditionally eliminates the entire high Ramanujan diagonal of
`PureSquare` (`O(n^{3/4} (log n)^2 τ(n))`), while Theorem 4 + PNT for `μ` eliminates `q ≤ n^{1/4}`! -/
theorem ramanujan_diagonal_tail_bound {n L : ℕ} (hn : 0 < n) (hL : 0 < L) (N : ℕ) :
    ∑ q ∈ Finset.Ioc L N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2
      ≤ (2 / (L : ℝ)) * (n.divisors.card : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  calc ∑ q ∈ Finset.Ioc L N, |(ramanujanSum q n : ℝ)| / (q : ℝ) ^ 2
      ≤ ∑ d ∈ n.divisors, (1 / (d : ℝ)) *
          ∑ k ∈ Finset.Ioc (L / d) (N / d), (1 : ℝ) / (k : ℝ) ^ 2 :=
        ramanujan_inv_sq_Ioc_le_divisor_sum hn L N
    _ ≤ ∑ _d ∈ n.divisors, (2 / (L : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
        have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
        have hsum := sum_inv_sq_Ioc_le (L / d) (N / d)
        by_cases hdiv0 : L / d = 0
        · rw [if_pos hdiv0] at hsum
          have hLd : L < d := (Nat.div_eq_zero_iff_lt hd_pos).mp hdiv0
          have hLdR : (L : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_of_lt hLd
          calc (1 / (d : ℝ)) * ∑ k ∈ Finset.Ioc (L / d) (N / d), (1 : ℝ) / (k : ℝ) ^ 2
              ≤ (1 / (d : ℝ)) * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
            _ = 2 / (d : ℝ) := by ring
            _ ≤ 2 / (L : ℝ) := div_le_div_of_nonneg_left (by norm_num) hLR hLdR
        · rw [if_neg hdiv0] at hsum
          have hm_pos : 0 < L / d := Nat.pos_of_ne_zero hdiv0
          have hmR : (0 : ℝ) < ((L / d : ℕ) : ℝ) := Nat.cast_pos.mpr hm_pos
          have hL_le : L ≤ 2 * d * (L / d) := by
            have h1 : L = d * (L / d) + L % d := (Nat.div_add_mod L d).symm
            have h2 : L % d < d := Nat.mod_lt L hd_pos
            have h3 : d ≤ d * (L / d) := Nat.le_mul_of_pos_right d hm_pos
            nlinarith
          have hL_leR : (L : ℝ) ≤ 2 * ((d : ℝ) * ((L / d : ℕ) : ℝ)) := by
            have : (L : ℝ) ≤ ((2 * d * (L / d) : ℕ) : ℝ) := by exact_mod_cast hL_le
            push_cast at this; linarith
          calc (1 / (d : ℝ)) * ∑ k ∈ Finset.Ioc (L / d) (N / d), (1 : ℝ) / (k : ℝ) ^ 2
              ≤ (1 / (d : ℝ)) * (1 / ((L / d : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
            _ = 1 / ((d : ℝ) * ((L / d : ℕ) : ℝ)) := by ring
            _ ≤ 2 / (L : ℝ) := by
                rw [div_le_div_iff₀ (by positivity) hLR]
                linarith
    _ = (2 / (L : ℝ)) * (n.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ### Theorem 6: Exact Farey Separation Lower Bound & Selberg–Ramanujan Reflection Identity -/

/-- **Theorem 6 (Exact Farey Separation Lower Bound on `ℝ / ℤ`)**:
For any two distinct reduced fractions `a₁ / q₁ ≠ a₂ / q₂` (`0 < q₁, q₂`, `a₁ < q₁`, `a₂ < q₂`,
`Nat.Coprime a₁ q₁`, `Nat.Coprime a₂ q₂`) and EVERY integer `k : ℤ`:
`1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)|`!
Combining this with Wave 26's Jordan bound gives `‖geomExpSum n (a₁/q₁ - a₂/q₂)‖ ≤ (q₁ * q₂) / 2`! -/
theorem farey_distinct_separation_lower_bound {q₁ q₂ a₁ a₂ : ℕ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (ha₁ : a₁ < q₁) (ha₂ : a₂ < q₂)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) (k : ℤ) :
    1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |(a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)| := by
  have hq1R : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr hq₁
  have hq2R : (0 : ℝ) < (q₂ : ℝ) := Nat.cast_pos.mpr hq₂
  have hnum_ne : (a₁ : ℤ) * (q₂ : ℤ) ≠ (a₂ : ℤ) * (q₁ : ℤ) := by
    intro heq
    have hN : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast heq
    have ⟨h1, h2⟩ := (coprime_frac_eq_iff hq₁ hq₂ hcop₁ hcop₂).mp hN
    exact hne (Prod.ext h1 h2)
  -- Show |(a₁ * q₂ - a₂ * q₁) - k * (q₁ * q₂)| ≥ 1 as integers!
  have hboundZ : (1 : ℤ) ≤ |(a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ))| := by
    have hup : (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) ≤ (q₁ : ℤ) * (q₂ : ℤ) - 1 := by
      have h1 : (a₁ : ℤ) + 1 ≤ (q₁ : ℤ) := by omega
      have h2 : (a₁ : ℤ) * (q₂ : ℤ) + (q₂ : ℤ) ≤ (q₁ : ℤ) * (q₂ : ℤ) := by nlinarith
      have h3 : (1 : ℤ) ≤ (q₂ : ℤ) := by omega
      have h4 : (0 : ℤ) ≤ (a₂ : ℤ) * (q₁ : ℤ) := by positivity
      linarith
    have hlo : -((q₁ : ℤ) * (q₂ : ℤ) - 1) ≤ (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) := by
      have h1 : (a₂ : ℤ) + 1 ≤ (q₂ : ℤ) := by omega
      have h2 : (a₂ : ℤ) * (q₁ : ℤ) + (q₁ : ℤ) ≤ (q₁ : ℤ) * (q₂ : ℤ) := by nlinarith
      have h3 : (1 : ℤ) ≤ (q₁ : ℤ) := by omega
      have h4 : (0 : ℤ) ≤ (a₁ : ℤ) * (q₂ : ℤ) := by positivity
      linarith
    have hqprod : (1 : ℤ) ≤ (q₁ : ℤ) * (q₂ : ℤ) := by nlinarith
    rcases lt_trichotomy k 0 with hkneg | rfl | hkpos
    · have hk_le : k ≤ -1 := by omega
      have hpos : (1 : ℤ) ≤ (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) := by
        nlinarith
      rw [abs_of_nonneg (by linarith)]; exact hpos
    · simp only [zero_mul, sub_zero]
      have hne0 : (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) ≠ 0 := sub_ne_zero.mpr hnum_ne
      exact Int.one_le_abs hne0
    · have hk_ge : 1 ≤ k := by omega
      have hneg : (a₁ : ℤ) * (q₂ : ℤ) - (a₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) ≤ -1 := by
        nlinarith
      rw [abs_of_nonpos (by linarith)]; linarith
  have hboundR : (1 : ℝ) ≤ |((a₁ : ℝ) * (q₂ : ℝ) - (a₂ : ℝ) * (q₁ : ℝ) - (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ)))| := by
    exact_mod_cast hboundZ
  have heq : (a₁ : ℝ) / (q₁ : ℝ) - (a₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)
      = ((a₁ : ℝ) * (q₂ : ℝ) - (a₂ : ℝ) * (q₁ : ℝ) - (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ))) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    field_simp [ne_of_gt hq1R, ne_of_gt hq2R]
  rw [heq, abs_div, abs_of_pos (mul_pos hq1R hq2R)]
  exact div_le_div_of_nonneg_right hboundR (le_of_lt (mul_pos hq1R hq2R))

/-- **Theorem 7 (Exact Selberg–Ramanujan Reflection Decomposition)**:
For any `n : ℕ` and any real functions `f, g : ℕ → ℝ` (e.g., `f = Λ`, `g = Λ_R`):
`∑ x ∈ Finset.Ico 1 n, f x * f (n - x)`
`= 2 * ∑ x ∈ Finset.Ico 1 n, f x * g (n - x) - ∑ x ∈ Finset.Ico 1 n, g x * g (n - x)`
`  + ∑ x ∈ Finset.Ico 1 n, (f x - g x) * (f (n - x) - g (n - x))`! -/
theorem selberg_ramanujan_reflection_identity (n : ℕ) (f g : ℕ → ℝ) :
    ∑ x ∈ Finset.Ico 1 n, f x * f (n - x)
      = 2 * ∑ x ∈ Finset.Ico 1 n, f x * g (n - x)
        - ∑ x ∈ Finset.Ico 1 n, g x * g (n - x)
        + ∑ x ∈ Finset.Ico 1 n, (f x - g x) * (f (n - x) - g (n - x)) := by
  -- Reflection symmetry: ∑_{x ∈ Ico 1 n} g x * f (n - x) = ∑_{x ∈ Ico 1 n} f x * g (n - x)
  have hsym : ∑ x ∈ Finset.Ico 1 n, g x * f (n - x) = ∑ x ∈ Finset.Ico 1 n, f x * g (n - x) := by
    refine Finset.sum_bij (fun x _ => n - x) ?_ ?_ ?_ ?_
    · intro x hx; rw [Finset.mem_Ico] at hx ⊢; omega
    · intro x₁ hx₁ x₂ hx₂ heq; rw [Finset.mem_Ico] at hx₁ hx₂; omega
    · intro y hy; rw [Finset.mem_Ico] at hy
      exact ⟨n - y, Finset.mem_Ico.mpr (by omega), by omega⟩
    · intro x hx; rw [Finset.mem_Ico] at hx
      rw [show n - (n - x) = x by omega, mul_comm]
  have hdiff : ∑ x ∈ Finset.Ico 1 n, (f x - g x) * (f (n - x) - g (n - x))
      = ∑ x ∈ Finset.Ico 1 n, f x * f (n - x)
        - ∑ x ∈ Finset.Ico 1 n, f x * g (n - x)
        - ∑ x ∈ Finset.Ico 1 n, g x * f (n - x)
        + ∑ x ∈ Finset.Ico 1 n, g x * g (n - x) := by
    have hpt : ∀ x ∈ Finset.Ico 1 n,
        (f x - g x) * (f (n - x) - g (n - x))
          = f x * f (n - x) - f x * g (n - x) - g x * f (n - x) + g x * g (n - x) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith

end GoldbachWave34
