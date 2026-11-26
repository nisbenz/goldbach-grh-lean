# B-011 — Zero-pair T^(3/2) log² T block: rigorous research analysis

**Date:** 2026-11-26. **Author:** research-analysis subagent (read-only on git).
**Scope:** answer the four delegated questions about B-011 using only local
sources plus scratch computation. **No proof of Goldbach, no proof of an
obstruction theorem, no status change, and no `checked` claim is made here.**
B-011 is `open` in `map/blockers.json` as of the last read.

## Label convention (same as `audit/ERH_ROUTE_ANALYSIS.md`)

| Tag | Meaning |
|---|---|
| **[Q]** | Quoted (verbatim or near-verbatim with line reference) from a repo file. |
| **[P]** | Paraphrased from a repo file; line reference given. |
| **[I]** | My inference / standard mathematical knowledge; **not** established by the repo. |
| **[U]** | "Supplied" paper cited in a repo doc but whose PDF is not in the repo; unverified. |
| **[SRC]** | Directly read from a local source (Mathlib cache), not a repo proof doc. |

Nothing here is `checked` under AGENTS.md §0: no Lean build and no checker run
were performed, and the audit already records that no repo theorem is
kernel-checked (`audit/REPO_AUDIT.md` §1 commands 4–6, §3).

### Desk / lease caveat (read this first)

The delegated lease command `python3 desk/desk.py next --holder agent-b011
--program analytic --hard` returned **B-004**, not B-011. That lease was
released immediately with reason `other: delegation targets B-011 but next
returned B-004; no work done`; no further `next` call was made (the CLI has no
blocker-id selector). `desk.py status` confirmed B-011 open/analytic/`research`/
`assigned_to: null` with zero active leases. **Therefore no B-011 lease was
held.** This document is the specifically delegated read-only analysis; the
parent must decide whether to accept it under a fresh proper lease and must not
attribute it to a lease that was never taken. No `map/`, `lean/`, `checker/`,
`news/` or clone file was written.

---

## 1. The exact kernel and the T^(3/2) log² T claim [Q], with the counting

### 1.1 Verbatim quotes [Q]

From `goldbach-grh-lean/proof/strong_goldbach_research.md`, §2 lines 100–118:

> **Keeping the zero phases.** Near zero the zeta explicit formula has oscillatory term
> `-\sum_\rho \Gamma(\rho)z^{-\rho},\qquad z=N^{-1}-2\pi i\beta .`  (line 102)

> On any fixed bounded β interval at fixed N this series is absolutely and uniformly convergent by the positive angular distance of z from the imaginary axis, Stirling's bound, and the zero count. Squaring it on an arc and integrating over that arc gives the genuine pair kernel
> `K_{w,N}(\rho,\rho')=\Gamma(\rho)\Gamma(\rho')\int_{-w}^{w} z^{-\rho-\rho'}e(-N\beta)\,d\beta . \tag{4}`  (lines 104–107)

> At a/q there are in addition the character coefficients, the factor e(-aN/q), and the residue, principal and cross terms from squaring. GRH sets both real parts in (4) to 1/2. It supplies neither the sign of (4) nor the cancellation across pairs or centers.  (line 109)

> For s=ρ+ρ' the full-line inverse transform of z^{−s} at positive N is e^{−1}N^{s−1}/Γ(s). ... For zeta zeros with positive ordinates T≤γ,γ'≤2T, Stirling gives `|Γ(1/2+iγ)Γ(1/2+iγ')/Γ(1+i(γ+γ'))| ≍ T^{−1/2}.`  (lines 111–114)

> The exponentials in Stirling cancel for the same sign. The Riemann–von Mangoldt formula gives ≍ T log T ordinates in the block, so the sum of the individual magnitudes of the inverted terms is ≍ T^{3/2}log²T. They retain the phases of the gamma quotient and of N^{i(γ+γ')}. At T≍N this block needs a factor of order N^{1/2}log²N to fall to linear scale if treated on its own.  (line 116)

> This second exponent calculation is for the specific full-line kernel, **not** a proof that one can extend every arc, sum this formula over all zeros or discard higher blocks. In particular the magnitude calculation precludes justifying that interchange by absolute summation. Opposite-sign pairs with comparable magnitudes have exponential damping and do not remove the same-sign difficulty.  (line 116)

> Summing the rational centers before estimating gives a twisted Gauss sum ... When q∣N and χ'=χ̄ it equals φ(q). Square-root cancellation in **every** such center sum is false. Even at q=1 the gamma-quotient phases remain. ... I have no GRH bound for that deficit.  (line 118)

The framework's own restatement [Q, `map/blockers.json` B-011]: "GRH fixes Re rho=1/2 but not cancellation in kernel (4); same-sign zero pairs with N^{i(gamma+gamma')} survive absolute summation", route "Weighted conductor-uniform pair-correlation after summing centers, at each even N; do not assume Montgomery pair correlation applies."

### 1.2 The counting, reconstructed [Q] + [I]

1. Under GRH/ERH, ρ = 1/2 + iγ and ρ' = 1/2 + iγ', so s = ρ+ρ' = 1 + i(γ+γ')
   and Re s = 1. [Q] line 109 / [I]
2. Full-line inversion gives e^{−1} N^{s−1}/Γ(s). Since Re s − 1 = 0,
   |N^{s−1}| = 1 and N^{s−1} = N^{i(γ+γ')} = exp(i(γ+γ') log N): a **pure phase**,
   unit modulus. [Q] line 111 + [I]
3. Multiplying by Γ(ρ)Γ(ρ') from (4): the inverted pair term is
   `e^{−1} N^{i(γ+γ')} · Γ(1/2+iγ)Γ(1/2+iγ') / Γ(1+i(γ+γ'))`, whose magnitude
   is ≍ T^{−1/2}. [Q] lines 111–114 + [I]
4. Riemann–von Mangoldt: N(T) ~ (T/2π)log(T/2π) − T/(2π) + O(log T), so
   N(2T) − N(T) ≍ T log T ordinates in [T,2T]. [Q] line 116 ("≍ T log T")
5. Same-sign **ordered** pairs in the block: (T log T)² ≍ T² log² T (unordered
   divides by 2 only; exponent unchanged). [I]
6. Sum of individual magnitudes: T^{−1/2} · T² log² T = **T^{3/2} log² T**. [Q] line 116
7. At T ≍ N this is ≍ N^{3/2} log² N. To fall to linear scale N one must divide
   by N^{1/2} log² N — i.e. cancellation of that size is required. [Q] line 116

The phrase "block [T, T+Δ]": the doc uses Δ = T ([T,2T]). For a narrower block
Δ = cT the same arithmetic gives Δ² log²T · T^{−1/2} ≍ c² T^{3/2} log² T;
for Δ = o(T) it is smaller. [I]

---

## 2. The magnitude cancellation, computed explicitly (Stirling exponent arithmetic)

### 2.1 Stirling modulus, written out [I]

For |arg z| < π − δ and |z| → ∞,
`log Γ(z) = (z − 1/2) log z − z + (1/2) log(2π) + O(1/|z|)`.

Put z = σ + it with t > 0 large. With log z = log|z| + i·arg z,
arg z = π/2 − σ/t + O(t⁻³), log|z| = log t + O(t⁻²):

```
Re log Γ(σ+it)
  = (σ−1/2) log|z| − t·arg z − σ + (1/2) log(2π) + O(1/t)
  = (σ−1/2) log t − t(π/2 − σ/t) − σ + (1/2) log(2π) + O(1/t)
  = (σ−1/2) log t − πt/2 + σ − σ + (1/2) log(2π) + O(1/t)
  = (σ−1/2) log t − πt/2 + (1/2) log(2π) + O(1/t).
```
Hence
```
|Γ(σ+it)| = √(2π) · t^{σ−1/2} · e^{−πt/2} · (1 + O(1/t)).      (★)
```

### 2.2 Apply (★) to the three Gamma factors [I]

Let T ≤ γ, γ' ≤ 2T (so 2T ≤ γ+γ' ≤ 4T and every ordinate is ≍ T).

```
log|Γ(1/2+iγ)|            = (1/2−1/2)log γ  − πγ/2       + (1/2)log(2π) + O(1/T)
                          =            0     − πγ/2       + (1/2)log(2π) + O(1/T)
log|Γ(1/2+iγ')|           =            0     − πγ'/2      + (1/2)log(2π) + O(1/T)
log|Γ(1+i(γ+γ'))|         = (1−1/2)log(γ+γ') − π(γ+γ')/2 + (1/2)log(2π) + O(1/T)
                          = (1/2)log(γ+γ')   − π(γ+γ')/2 + (1/2)log(2π) + O(1/T)
```

**Numerator log-modulus** (sum of first two):
```
log(2π) − (π/2)(γ+γ') + O(1/T).
```
**Denominator log-modulus:**
```
(1/2)log(γ+γ') − (π/2)(γ+γ') + (1/2)log(2π) + O(1/T).
```
**Subtract** — the exponential terms cancel *exactly*:
```
[log(2π) − (π/2)(γ+γ')] − [(1/2)log(γ+γ') − (π/2)(γ+γ') + (1/2)log(2π)]
   = log(2π) − (1/2)log(2π) − (1/2)log(γ+γ')  + [−π(γ+γ')/2 + π(γ+γ')/2]
   = (1/2)log(2π) − (1/2)log(γ+γ') + O(1/T)
   = log( √(2π)/√(γ+γ') ) + O(1/T).
```
Therefore
```
|Γ(1/2+iγ)Γ(1/2+iγ')/Γ(1+i(γ+γ'))| = √(2π)·(γ+γ')^{−1/2}(1+O(1/T)) ≍ T^{−1/2},
```
because 2T ≤ γ+γ' ≤ 4T gives (γ+γ')^{−1/2} ∈ [1/(2√T), 1/(√2√T)]. This is
exactly the doc's bound [Q] line 114. The "[I] exponentials cancel for the same
sign" remark [Q] line 116 is the cancellation of the two −π(γ+γ')/2 terms
displayed above; it is an exact cancellation of the *dominant exponential*, not
a cancellation of the phases.

**Sharper than Stirling (also [I] + numerical):** the reflection identities
`|Γ(1/2+it)|² = π/cosh(πt)` and `|Γ(1+it)|² = πt/sinh(πt)` give the *exact*
modulus
```
|Γ(1/2+iγ)Γ(1/2+iγ')/Γ(1+i(γ+γ'))|
   = √[ π/cosh(πγ) · π/cosh(πγ') · sinh(π(γ+γ'))/(π(γ+γ')) ]
   = √(2π)/√(γ+γ') · (1 + O(e^{−2π min(γ,γ')})),
```
so the T^{−1/2} decay is exponentially accurate, not merely asymptotic. Scratch
check (100 zeros, 10⁴ pairs): the ratio of the exact modulus to
e^{−1}√(2π)/√(γ+γ') had max deviation 1.7×10⁻²⁸ — consistent with the
exponentially small correction. (The e^{−1} here is the constant from the
full-line inverse transform; the doc's ≍ absorbs it.)

### 2.3 Opposite-sign pairs are exponentially damped [Q] + [I]

Take γ' = −γ'' with γ'' > 0. Then the numerator exponentials are
e^{−πγ/2}·e^{−πγ''/2} = e^{−π(γ+γ'')/2}, while the denominator is
|Γ(1+i(γ−γ''))| ≈ √(2π)|γ−γ''|^{1/2} e^{−π|γ−γ''|/2}. When γ ≈ γ'' the
denominator exponential is ≈ 1, so the quotient is ≈
√(2π) e^{−π(γ+γ'')/2}/|γ−γ''|^{1/2}, exponentially small (≍ e^{−πT}). Hence
opposite-sign pairs do not cancel the same-sign block. [Q] line 116:
"Opposite-sign pairs with comparable magnitudes have exponential damping and do
not remove the same-sign difficulty." ✓ confirmed.

### 2.4 Confirm or correct the doc's T^{3/2} log² T [I]

**Confirmed**, for the precise quantity the doc computes: the *sum of individual
magnitudes* of the full-line inverted pair terms over the block [T,2T].

```
#pairs ≍ (T log T)² = T² log² T;   magnitude per pair ≍ T^{−1/2};
absolute sum ≍ T^{−1/2}·T² log² T = T^{3/2} log² T.
```

At T ≍ N this is ≍ N^{3/2} log² N, needing a factor N^{1/2} log² N of
cancellation to reach linear scale — the doc's statement [Q] line 116. ✓

Three honest qualifications, all [I]:
- This is a **triangle inequality** (absolute) estimate. It is an upper bound on
  |Σ signed terms| only in the wrong direction: |Σ| ≤ Σ|·| ≍ T^{3/2} log² T ≫ N,
  so absolute summation yields **no** usable pointwise bound. It is not a claim
  that the signed sum is actually that large.
- The full-line inverse is a **diagnostic** replacing the arc integral
  ∫_{−w}^{w} in (4); the doc says so explicitly [Q] line 116. Extending arcs,
  summing all zeros, or discarding higher blocks is not justified here.
- The phases survive: N^{i(γ+γ')} = exp(i(γ+γ')log N) and the Stirling gamma
  quotient phase exp(i[θ(γ)+θ(γ')−θ(γ+γ')]) with θ(t) ≈ t log t − t + … . Both
  have unit modulus, so |·| estimates cannot discard them; only **cancellation
  between different pairs** can. GRH/ERH supplies no such cancellation.

Center sums do not rescue it [Q] line 118: for q ∣ N and χ' = χ̄ the Gauss sum
Σ*_{a mod q} χ(a)χ̄(a)e(−aN/q) = φ(q), not √q; square-root cancellation fails in
every such center, and at q = 1 the gamma-quotient phases remain.

---

## 3. One concrete, checkable micro-step — PROPOSED

### 3.1 The proposed lemma (finite geometric-sum cancellation of unit phases) [I]

This is the elementary model for the only kind of step that can beat §2.4: a
**signed** cancellation in a sequence of unit phases. It is stated so a parent
can submit it directly; it is **PROPOSED, not written to `lean/`, not built, not
checked**.

```lean
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Goldbach.B011

/-- Unit modulus of a single zero-pair phase. (Already Mathlib:
    `Complex.norm_exp_ofReal_mul_I`, tagged [simp] — see §3.2.) -/
lemma norm_pair_phase (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
  simpa using Complex.norm_exp_ofReal_mul_I θ

/-- (PROPOSED B-011 micro-step) Cancellation of a finite progression of unit
    phases. This is the toy model for the cancellation required from the
    N^{i(γ+γ')} phases in the off-diagonal sum: a triangle bound gives M here,
    while this lemma gives 2/‖1 - q‖ whenever q ≠ 1. -/
theorem norm_sum_exp_progression_le (θ : ℝ) (M : ℕ)
    (hθ : Complex.exp (θ * Complex.I) ≠ 1) :
    ‖∑ j ∈ Finset.range M, Complex.exp ((j : ℝ) * θ * Complex.I)‖
      ≤ 2 / ‖1 - Complex.exp (θ * Complex.I)‖ := by
  let q : ℂ := Complex.exp (θ * Complex.I)
  have hq : q ≠ 1 := hθ
  have hpow : ∀ j : ℕ, Complex.exp ((j : ℝ) * θ * Complex.I) = q ^ j := by
    intro j
    simp [q, ← Complex.ofReal_natCast, ← mul_assoc, ← Complex.exp_nat_mul]
  rw [show (∑ j ∈ Finset.range M, Complex.exp ((j : ℝ) * θ * Complex.I))
        = ∑ j ∈ Finset.range M, q ^ j by exact Finset.sum_congr rfl (fun j _ => hpow j)]
  rw [geom_sum_eq hq M]
  calc
    ‖(q ^ M - 1) / (q - 1)‖ = ‖q ^ M - 1‖ / ‖q - 1‖ := by rw [Complex.norm_div]
    _ ≤ (‖q ^ M‖ + ‖(1 : ℂ)‖) / ‖q - 1‖ := by
          gcongr
          simpa [sub_eq_add_neg] using norm_add_le (q ^ M) (-1)
    _ = 2 / ‖1 - q‖ := by
          rw [Complex.norm_pow, norm_pair_phase]
          simp [norm_sub_rev]
end Goldbach.B011
```

**Proof sketch (PROPOSED, unverified).** Let q = exp(iθ). Rewrite each summand
as q^j via `Complex.exp_nat_mul`; apply `geom_sum_eq hq M` (verified name,
`Mathlib/Algebra/Field/GeomSum.lean:43`: `∑ i ∈ range n, x^i = (x^n − 1)/(x−1)`
for x ≠ 1). `Complex.norm_div` splits the quotient; `norm_add_le` gives
‖q^M − 1‖ ≤ ‖q^M‖ + 1 = 2 because ‖q‖ = 1 by `Complex.norm_exp_ofReal_mul_I`
and `Complex.norm_pow`. Finally ‖q − 1‖ = ‖1 − q‖ by `norm_sub_rev`. Anticipated
API adjustments at build time: the exact name/shape of `Complex.exp_nat_mul`
and of the cast rewrite for `(j : ℝ) * θ`; if missing, prove the two-line
induction `exp((j+1)θI) = exp(jθI)·exp(θI)` inline (AGENTS.md §3: helpers in one
file). No new axioms, no `native_decide`.

**What this lemma does and does not establish [I].** It proves that *if* the
relevant phases behave like an arithmetic progression in θ, the sum is O(1/θ)
rather than O(M). It does **not** prove that zeta-zero sums γ+γ' (nor the
gamma-quotient phase) are of that form; that is precisely the unproved analytic
input (B-011's route). Its value is to make the "cancellation vs absolute sum"
distinction kernel-checkable and reusable.

### 3.2 Source anchors [SRC]

- `Mathlib/Analysis/Complex/Trigonometric.lean:949-950`:
  `@[simp] theorem norm_exp_ofReal_mul_I (x : ℝ) : ‖exp (x * I)‖ = 1`.
- `Mathlib/Analysis/Complex/Trigonometric.lean:983`:
  `theorem norm_exp (z : ℂ) : ‖exp z‖ = Real.exp z.re`.
- `Mathlib/Analysis/Complex/Norm.lean:75-77`:
  `@[simp] protected theorem norm_mul`, `norm_div`.
- `Mathlib/Algebra/Field/GeomSum.lean:43`: `geom_sum_eq`.

**Key honest finding [I]:** the "phase survives with unit modulus" ingredient is
already in Mathlib and is `[simp]`. The B-011 blocker is therefore **entirely**
in the analytic cancellation across the zero pairs — not in formalizing the
phase magnitudes. A proposed dependency chain for a parent: prove §3.1 (easy),
then attempt the genuinely hard lemma bounding the signed pair sum.

### 3.3 Optional numerical diagnostic (supplementary, [I], not checked)

Scratch `mpmath` 1.3.0 experiment on the first 100 zeta zeros
(`/tmp/opencode/b011/numerics.py`, output `numerics.txt`): actual ordinates
γ ∈ [14.134725, 236.52423], GRH Re ρ = 1/2 imposed exactly as in the doc's
diagnostic. For each fixed N, over all 10⁴ ordered pairs, term =
`e^{−1}·N^{i(γ+γ')}·Γ(1/2+iγ)Γ(1/2+iγ')/Γ(1+i(γ+γ'))`.

| N | Σ‖term‖ (triangle) | ‖Σ term‖ | cancellation ratio | phase-only ‖Σ‖/#pairs |
|---|---:|---:|---:|---:|
| 10³ | 578.0756 | 5.8004 | 0.01003 | 0.00413 |
| 10⁴ | 578.0756 | 15.9244 | 0.02755 | 0.01139 |
| 10⁶ | 578.0756 | 8.9875 | 0.01555 | 0.02611 |

- The magnitude per term matched e^{−1}√(2π)/√(γ+γ') with max relative
  deviation 1.7×10⁻²⁸ — strongly confirming §2.2 numerically.
- The phases do produce large *relative* cancellation (|Σ| ≈ 1–3 % of Σ|·|) at
  these fixed N — but this is a **tiny, non-asymptotic sample**: 100 zeros in
  [14,237], not a full dyadic block at T ≍ N with ≍ T log T zeros. It is
  **evidence, not a theorem**, and says nothing about uniformity in N or about
  the T ≍ N regime. It neither proves nor refutes the block.

---

## 4. Honest verdict: does this block survive ERH / Grand RH?

**Short answer [I]: Yes, as far as the repo's framework records it.** The
T^{3/2} log² T absolute-magnitude block is computed *under* GRH; relabelling
GRH as ERH changes nothing ([I], consistent with `audit/ERH_ROUTE_ANALYSIS.md` §2:
on the Dirichlet family "GRH" already *is* ERH). Grand RH (all automorphic
L-functions) likewise strengthens the zero-location class but supplies no
pair-correlation/cancellation for the zeta ordinates γ+γ' appearing in (4). No
hypothesis of "location" type fixes the sign of (4). [I/[Q]]

Evidence, all labelled:

1. **[Q]** `research.md:109`: GRH sets Re ρ = Re ρ' = 1/2 but "supplies neither
   the sign of (4) nor the cancellation across pairs or centers."
2. **[Q]** `research.md:116`: the T^{3/2} log² T calculation and the surviving
   phases are stated *under* GRH; the caveat explicitly says it is not a proof
   about extending arcs/summing zeros/discarding blocks.
3. **[Q]** `research.md:118`: center sums with q ∣ N, χ' = χ̄ give φ(q), so even
   summing rational centers cannot be relied on for square-root cancellation.
4. **[I]** The phases that survive, N^{i(γ+γ')} and the gamma-quotient phase,
   have unit modulus (§3.2: Mathlib already proves this). An |·| estimate cannot
   remove them; only signed cancellation between pairs can.
5. **[I/Q]** Even a proved Montgomery pair correlation would not directly
   apply: it concerns differences γ − γ', whereas (4) involves **sums** γ + γ'
   (same-sign pairs). Audit `REPO_AUDIT.md` blocker 6 records exactly this:
   "pair correlation involves sums γ+γ', not differences." The repo's route
   accordingly says "do **not** assume Montgomery pair correlation applies"
   (B-011 `route` field).
6. **[Q]** `research.md:3` / `audit/REPO_AUDIT.md` C19: the repo claims no proof
   of pointwise strong Goldbach even under Dirichlet GRH; the audit explicitly
   calls this "an honest limitation of the repo, not a theorem of independence."

**What would be needed to break it [I].** A genuinely two-input, signed estimate
that retains the common phase, valid uniformly in the conductor and pointwise
in the even target N — e.g. a weighted conductor-uniform correlation for sums
over pairs (γ,γ') that controls
`Σ_{γ,γ'} Γ(ρ)Γ(ρ') e^{−1} N^{i(γ+γ')}/Γ(ρ+ρ')` at scale o(N), *after* summing
centers, with the γ+γ' (not γ−γ') structure handled directly; or bypassing the
zero-pair expansion altogether via a signed minorant / two-form (dispersion)
estimate. None of H1/H2/H3, the exceptional-set theorem, or Montgomery-style
inputs supplies this, and the parity/reflection obstructions (audit C21/C22/C35)
defeat the specified weaker deductions. This is a statement about missing proof
strategies, **not** a proof that Goldbach is false or independent of ERH.

**Verdict:** B-011 remains `open`; no `checked` proof and no `checked` refutation;
pointwise Strong Goldbach stays **open under ERH (and under Grand RH as recorded
here)**. No status change was made by this agent.

---

## 5. What was and was not done (no success claims)

- **Read in full:** `AGENTS.md`, `ARCHITECTURE.md`, `audit/REPO_AUDIT.md`,
  `audit/ERH_ROUTE_ANALYSIS.md`; targeted read of
  `goldbach-grh-lean/proof/strong_goldbach_research.md:96-135`; source reads in
  the local Mathlib cache (§3.2).
- **Commands:** desk `next`/`release`/`--help`/`status`/`blockers` (lease only);
  greps over the Mathlib cache; `mpmath` 1.3.0 scratch computation in
  `/tmp/opencode/b011/`.
- **Not done:** no Lean build, no `checker/strict_check.py` run, no submission,
  no beat, no map/feed/claim change, no git operation, no arXiv fetch. The one
  PROPOSED lemma (§3.1) is **not** written to `lean/` and **not** verified.
- **No arXiv paper was used;** no [U] claims occur in this document.
- **No claim is made** that Goldbach is true or false, that B-011 is resolved,
  or that any theorem here is `checked`.

### Files written (only these two, as delegated)

- `agents/CHECKPOINT_B-011.md`
- `audit/B011_ZEROPAIR_ANALYSIS.md` (this file)

Final byte sizes are recorded in `agents/CHECKPOINT_B-011.md` at close.

---

## Lease and status

- Lease taken properly with `python3 desk/desk.py next --holder agent-b011 --id B-011`
  (the desk tool now supports `--id`). **Lease id:
  `f2d1bd3f81f64d87a69347d2358159b7`**, blocker `B-011`, holder `agent-b011`.
  The desk confirmed the blocker as `open`, program `analytic`, difficulty
  `research`, `parallel 5`.
- **B-011 remains `open`.** No claim/blocker status, map, feed, `lean/`,
  `checker/` or `news/` file was changed; no git operation was performed.
- **This analysis claims no proof.** It is a read-only research analysis: no
  `checked` theorem, no proof or refutation of Goldbach, no kernel build and no
  checker verdict. The Lean lemma in §3.1 is **PROPOSED only** (unwritten,
  unbuilt, unverified), and the numerical diagnostic in §3.3 is non-asymptotic
  evidence, not a theorem. B-011 stays open under ERH and Grand RH as recorded
  in §4.
- Lease released at the end of this work with reason
  `analysis_complete_no_proof`; no `beat` was needed (well under 30 minutes).
