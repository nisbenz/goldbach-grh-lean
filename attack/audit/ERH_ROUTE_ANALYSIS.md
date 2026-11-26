# ERH route analysis for blocker B-002

**Date:** 2026-11-26. **Author:** subagent (research analysis; read-only on git).
**Scope:** answer the four questions in the B-002 delegation using only local
sources. **No proof of Goldbach, no status change, no claim of `checked` is made
here.** B-002 remains `open` in `map/blockers.json` as of the last read.

## Label convention (applies to every claim below)

| Tag | Meaning |
|---|---|
| **[Q]** | Quoted (verbatim or near-verbatim with line reference) from a repo file. |
| **[P]** | Paraphrased from a repo file; line reference given. |
| **[I]** | My inference / standard mathematical knowledge; **not** established by the repo. |
| **[SRC]** | Directly read from a local source file (Mathlib/AINTLIB cache), not a repo proof doc. |
| **[U]** | "Supplied" paper cited in a repo doc but whose PDF is **not** in the repo; **unverified**. Audit §4 lists these explicitly. |

Nothing in this document is `checked` under AGENTS.md §0: no Lean build was run
here, and the audit already records that no repo theorem is kernel-checked
(`audit/REPO_AUDIT.md` §1 commands 4–6, §3). A doc's conditional theorem stays
conditional in every line below.

---

## 1. What ERH is, and how it differs from GRH

### 1.1 Standard definition (not from the repo) — [I]

Let `q ≥ 1` and let `χ` be a Dirichlet character mod `q`. The Dirichlet
L-function is

```
L(s, χ) = ∑_{n≥1} χ(n) n^{-s}        (Re s > 1),
```

with meromorphic continuation to `ℂ`: entire when `χ` is nonprincipal, with a
simple pole at `s = 1` when `χ` is principal. Its completed form is

```
Λ(s, χ) = (q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ),
a = 0 if χ(-1) = +1 (even),  a = 1 if χ(-1) = −1 (odd),
```

satisfying `Λ(s, χ) = i^{-a} τ(χ) q^{-1/2} Λ(1−s, χ̄)`. The **trivial** zeros
lie at `s = −a, −a−2, −a−4, …`; the remaining zeros in the critical strip
`0 < Re s < 1` are **nontrivial**.

**ERH (extended Riemann hypothesis):** for every **primitive** Dirichlet
character `χ` of every conductor `q ≥ 1` — including the principal character of
conductor 1, i.e. the Riemann zeta function — every nontrivial zero `ρ` of
`L(s, χ)` satisfies `Re ρ = 1/2`.

Equivalent nonvanishing form: `L(s, χ) ≠ 0` for `Re s > 1/2`, apart from the
pole of `ζ` at `s = 1`. **RH** is the special case `q = 1`.

### 1.2 How the repo uses the words — [Q] / [P]

- **[Q]** `proof/weak_goldbach_proof.md:3-4`: "Assume every nontrivial zero of
  every primitive Dirichlet $L$-function, including the Riemann zeta function,
  has real part $1/2$." That is exactly ERH, called "GRH" in the doc's title.
- **[P]** `audit/REPO_AUDIT.md:186`: the binary exceptional-set result assumes
  "GRH for all primitive Dirichlet characters **including conductor 1**".
- **[P]** `proof/strong_goldbach_research.md:24-28`: Theorem 1 assumes
  "Dirichlet GRH" and remarks that *only* RH for zeta is needed on the major
  arcs.
- **[P]** `proof/strong_goldbach_erh_attack.md:18-23` additionally assumes
  **Artin holomorphy** for the twists `ρ ⊗ χ` to get its Chebotarev estimate
  (1); §4 uses **automorphic RH**; blocker 13 (audit line 278) names "Grand RH
  for all GL_n".

**Inference [I]:** on the Dirichlet family, "Dirichlet GRH" = ERH — they are
the same hypothesis, not two strengths. The repo's phrase "GRH" in its analytic
sections is already the user's "ERH". Therefore *relabelling* GRH as ERH buys
**no** new exponent in the repo's error terms (see §2). The wider terminology
is strictly stronger in scope: **Dedekind/Artin GRH** asserts the analogous
statement for all `ζ_K` (equivalently Artin L-functions); for abelian `K`,
`ζ_K` factors into Dirichlet L-functions, so ERH implies that case [I], while
nonabelian `K` is not covered by ERH; conversely Dedekind GRH implies ERH
because `L(s,χ)` divides `ζ_K` for the cyclic field attached to `χ` [I].
**Grand RH** (all automorphic L-functions) is stronger still. The repo never
claims any of these stronger hypotheses closes the gap.

### 1.3 Mathlib definitions — [SRC]

Searched: `/home/eequaled/lean-lake-cache/packages/mathlib/Mathlib/` and the
other cached packages. Findings:

1. **Mathlib has a zeta RH `Prop`, and nothing for Dirichlet GRH/ERH.**
   `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:182-186`:

   ```lean
   /-- A formal statement of the **Riemann hypothesis** ... -/
   @[wikidata Q205966]
   def RiemannHypothesis : Prop :=
     ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
       (_ : s ≠ 1), s.re = 1 / 2
   ```

2. **[SRC]** `Mathlib/NumberTheory/LSeries/Dirichlet.lean` (header, lines
   16–35) provides Dirichlet L-*series*, e.g.
   `DirichletCharacter.LSeries_ne_zero_of_one_lt_re` on `re s > 1` and
   `DirichletCharacter.absicssaOfAbsConv_eq_one`. A grep for
   `RiemannHypothesis|GeneralizedRiemann|ExtendedRiemann|GRH` across all cached
   packages found **only** the zeta definition above inside Mathlib. I found no
   Mathlib definition of a *completed* Dirichlet L-function, its functional
   equation, or its critical-strip zeros. So **there is no Mathlib ERH
   definition to import**; one must postulate it as a named `Prop` first.
   (I did not verify the full LSeries API by building; this is a source-level
   search, not a `lake build`.)

3. **[SRC]** Precedent in a **sibling project, not Mathlib**:
   `/home/eequaled/lean-lake-cache/packages/AINTLIB/projects/DedekindResidue/DedekindResidue/CompletedZeta/GRH.lean:40-42`:

   ```lean
   def GeneralizedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
     ∀ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ →
       ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Λ s ≠ 0
   ```

   Its header (lines 24–26) stresses GRH is "threaded as a **hypothesis
   argument** — never an `axiom` — so every result stays axiom-clean". This is
   the right modelling pattern for ERH: quantify over a completed-L object
   given by an interface/caracterisation, and state nonvanishing on
   `Re s > 1/2`, rather than declaring an axiom. It is *not* an ERH definition,
   and that project is unverified here.

**Conclusion for question 1:** Mathlib defines only `RiemannHypothesis` for
`ζ`; **no** ERH / Dirichlet-GRH `Prop` exists in Mathlib. A Lean ERH statement
must be introduced as a named hypothesis, following the AINTLIB pattern, with
the primitive-character quantifier and the conductor-1 case made explicit.

---

## 2. What ERH buys beyond GRH in the circle-method error terms

### 2.1 The short answer — [I]

**Nothing, in the repo's sense of "GRH".** Every error term the repo attributes
to "Dirichlet GRH" is already an ERH term (§1.2). The explicit exponents in
`strong_goldbach_research.md` and `strong_goldbach_erh_attack.md` do not improve
when "GRH" is renamed "ERH". What *would* add information is strictly stronger:
Artin holomorphy + ERH for the twists `ρ ⊗ χ` (erh_attack.md §1, eq. (1)), or
automorphic RH (§4, eq. (7)), or Grand RH (audit blocker 13). Even those, the
docs say, do not close the pointwise gap.

### 2.2 The exact exponents stated in the docs

**(a) The 1/4 mean-square gap** — `strong_goldbach_research.md:96-98`:

- **[P]** In the companion binary proof's Farey dissection,
  `E_n = Ŝ²−M²(n)` satisfies `∑_{n≥1}|E_n|² ≤ 1600 N^{5/2} L³` at scale `X=N`
  (GRH estimate).
- **[P]** Over a block of order `N` integers this gives root-mean-square size
  `O(N^{3/4} L^{3/2})` (since `√(N^{5/2}L³ / N) = N^{3/4}L^{3/2}` — [I]
  arithmetic check).
- **[Q]** "For a *specified* coefficient its entire allowance is
  $40N^{5/4}L^{3/2}$" (i.e. `√1600·N^{5/4}L^{3/2}` — [I]).
- **[Q]** "Compared with a fixed positive multiple of $N$ the exponent gap for
  this deduction is **exactly $1/4$**, plus logarithms. An isolated negative
  error of size $N$ consumes just $N^2$ of the squared budget."
- **[Q]** "This is a diagnosis of that theorem, not a lower bound on the actual
  error or on losses in every circle method." Also [P]: quasi-RH fourth-moment
  exceptional counts still permit an isolated exception, and the
  exceptional-set theorem is about a different model from (H1), so its average
  cannot be substituted for (H1).

**(b) The `T^{3/2} log²T` zero-pair block** — `strong_goldbach_research.md:100-118`:

- **[P]** The zeta explicit formula near zero has oscillatory term
  `−Σ_ρ Γ(ρ) z^{−ρ}`, `z = N^{−1} − 2πiβ`; squaring on an arc gives the kernel
  `K_{w,N}(ρ,ρ') = Γ(ρ)Γ(ρ') ∫_{−w}^{w} z^{−ρ−ρ'} e(−Nβ) dβ` — eq. (4).
- **[P]** GRH sets `Re ρ = Re ρ' = 1/2` (hence `Re(ρ+ρ')=1`) but supplies
  neither the sign of (4) nor cancellation across pairs/centres.
- **[Q]** For the full-line diagnostic, the inverse transform of `z^{−s}` at
  positive `N` is `e^{−1}N^{s−1}/Γ(s)`, and for positive ordinates
  `T ≤ γ,γ' ≤ 2T`, Stirling gives
  `|Γ(1/2+iγ)Γ(1/2+iγ') / Γ(1+i(γ+γ'))| ≍ T^{−1/2}`.
- **[Q]** Riemann–von Mangoldt gives `≍ T log T` ordinates in the block, "so the
  sum of the individual magnitudes of the inverted terms is
  $\asymp T^{3/2}\log^2T$" (`T^{−1/2}·(T log T)²` — [I]). "At $T\asymp N$ this
  block needs a factor of order $N^{1/2}\log^2N$ to fall to linear scale if
  treated on its own." The phases `N^{i(γ+γ')}` and of the gamma quotient
  survive; opposite-sign pairs are exponentially damped.
- **[Q]** Caveat verbatim: "This second exponent calculation is for the
  specific full-line kernel, **not** a proof that one can extend every arc,
  sum this formula over all zeros or discard higher blocks. In particular the
  magnitude calculation precludes justifying that interchange by absolute
  summation." **[P]** Centres: for `q | N`, `χ' = χ̄`, the Gauss sum equals
  `φ(q)`, so square-root cancellation in *every* centre sum is false; GRH does
  not even assert Montgomery pair correlation.

**(c) The unconditional spectral benchmark** — `strong_goldbach_erh_attack.md:35-71`:

- **[Q]** For `d ≤ N`, `∑_{m≡a mod d} d₂(m) H(m/N) = M_d(a;H) +
  O_{ε,H}(N^ε d^{1/2})` — eq. (2), and "Both (2) and (3) already hold
  unconditionally." Summing absolute remainders gives `O(N^ε D^{3/2})`, i.e.
  **[P]** level `2/3 − δ`.
- **[Q]** Reflected sum: `∑_{m=1}^{N−1} W(m/N)d₂(m)d₂(N−m) =
  2∑_{d≤2√N} M_d(N;H_d) + O_{ε,W}(N^{3/4+ε})` — eq. (3). Gain comes from
  Voronoi dual length `≈ q²/N` plus Weil.
- **[P]** Audit C23 marks the `N^{3/4+ε}` claim **UNVERIFIED** here (doc read,
  not re-derived; no machine check). No ERH is involved in (2)/(3).

**(d) What the stronger hypotheses give, per the docs**:

- **[P]** `erh_attack.md:18-27` eq. (1): Artin holomorphy + ERH for `ρ⊗χ`
  gives `∑_{p≤N, p≡N mod d}(\log p) f(Frob_p) =
  Nδ_{K,f}(d,N) + O_{K,f}(√N log²(2Nd))`; summing `d ≤ D` costs
  `O(D√N log²(2ND))` and "supplies every fixed exponent below 1/2", no larger.
  **[Q]** "Chebotarev in the compositum imposes simultaneous splitting
  conditions on a *single* prime. It supplies no such two-input count."
- **[P]** `erh_attack.md:132-137` eq. (7): under automorphic RH + temperedness,
  `|Σ_{d|n}(a⁺_n−a⁻_n)A_π(n)V(n/N)| ≪ N^η (N/d)^{1/2+η}` for squarefree
  `d ≤ N` coprime to `N`, giving a power saving at every fixed level `< 1`.
  Audit C24: **CONDITIONAL** (automorphic RH, temperedness, Lindelöf, local
  Ramanujan).
- **[P]** `research.md:24-44, 84-95, 197-208`: the explicit major-arc side is
  computed under GRH/RH: (H1) `F_N(𝕋∖A) ≥ −0.764480N` with
  `2J(17/4) > 0.764483`, errors `d_N < 8.2·10⁻⁷` and `b_N < 2.3·10⁻⁸N`,
  leaving margin `> 2·10⁻⁶N`; (H2) `F_N(𝕋∖A_y) > −NJ(T_y)D_H(N) + Nd_y + b_N`,
  with `J(T_y)>0.292`, `D_H>1.15`, `d_y<0.00003`, uniform `F ≥ −N/3`
  sufficient; (H3) `U_N ≥ −(1−1.05·10⁻⁷)κN` with total loss
  `< 1.05·10⁻⁷` at `√C = 2·10⁹`.
- **[P]** `erh_attack.md:186-198` eqs. (8)–(9): one-sided reductions are
  conditional on the **unproved** bias bounds
  `H(N) ≤ (f_*−ε)N V_N(z)`, `f_* = (8e^γ/9)log(5/4)`, and
  `limsup B_C(N)L²/(𝔖(N)N) < c`; audit C25/C26.

### 2.3 Proved / conjectured / hand-waved ledger (exact labels)

| Item | Status in the doc | Audit status | Our label |
|---|---|---|---|
| Major-arc constants `J(T)`, `J(T_y)`, `D_H`, `d_N`, `b_N`; H1/H2/H3 reductions | **[P]** derived in doc, "no gap between the finite and analytic endpoints" (`research.md:212`) | C20 CONDITIONAL (H1–H3 unproved, not Lean-checked) | conditional reduction; input conjectured |
| `1/4` exponent gap, `T^{3/2}log²T` block | **[Q]** "diagnosis of that theorem" / "not a proof that one can extend every arc" | C23-adjacent research calculations | **not** proved; obstruction estimate |
| (2) `d₂` level `2/3−δ`, (3) reflected `N^{3/4+ε}` | **[Q]** "already hold unconditionally" | C23 UNVERIFIED (source read only) | doc-claimed unconditional, machine-unverified |
| Chebotarev twist (1) | **[P]** needs Artin holomorphy + ERH | not separately numbered | conjectural input |
| Automorphic parity theorem (7) | **[P]** conditional on automorphic RH + temperedness + Lindelöf | C24 CONDITIONAL | conditional theorem about a *model* |
| (8) `z=N^{2/9}`, (9) Chen one-sided | **[P]** need `H(N)`, `B_C(N)` biases | C25/C26 CONDITIONAL | unproved signed inputs |
| LWW Remark 3, GWX Hyp. 1.1, Pascadi, Li–Liu, WEH(0.999) | **[P]** used at "supplied" strength | C27–C32 CONDITIONAL, PDFs absent | **[U]** unverified |
| "ERH closes the pointwise gap" | **[Q]** nowhere claimed; `erh_attack.md:3`: "I obtain no proof … under the hypotheses in the question"; `research.md:3`: "I find no proof … even assuming Dirichlet GRH" | C19 (repo's own conclusion) | **not claimed** |

---

## 3. One concrete, checkable micro-step to formalize next

### 3.1 Why the other candidates are rejected — [I]

- **(a) "State ERH as a Prop with correct definitions."** Too large as stated:
  Mathlib has no completed Dirichlet L-function or critical-strip zeros (§1.3),
  so a correct ERH `Prop` first requires that analytic interface (functional
  equation, conductor, primitive characters, zero set). A *schema* quantified
  over an abstract completed-L object could be written, but would not be a
  statement about genuine Dirichlet L-functions and would risk vacuity. Better
  to defer until the interface exists, then follow the AINTLIB GRH pattern.
- **(b) "Finite zero-free-region check for small conductor."** Requires rigorous
  high-precision evaluation of `L(s,χ)` / Turing zero counting; no such
  interval-arithmetic API is available locally, and this is not a Lean
  micro-step. This is a research/computation project, not a blocker-sized task.
- **(c) "Combinatorial lemma with no analytic dependency."** **Chosen** below.

### 3.2 Proposed blocker B-017 (proposed, subordinate to B-002) — [I]

**Title:** Kernel-check the exact Liouville prime-detector identity on
cube-root-rough complements.
**Program:** `found`. **Difficulty:** easy–medium (API wrestling with
`primeFactorsList`, not mathematics). **Status:** PROPOSED ONLY — not written,
not built, not proved, not added to `map/` (writes restricted).

**Source of the statement:** `proof/strong_goldbach_erh_attack.md:97-103`,
eq. (5) **[Q]**: "Take `z=N^{1/3}` … restrict to `1<m<N, P^-(m)>z`. Such an
`m` is a prime, a product of two distinct primes, or a prime square.
Consequently $1_{\mathbb P}(m)=\frac{\mu^2(m)-\mu(m)}2=\frac{1-\lambda(m)}2$,
$\lambda(m)=(-1)^{\Omega(m)}$." **[P]** The doc uses this to correct the
suggested `(1−μ(m))/2`, which misweights prime squares, and it underlies both
one-sided reductions (8) and (9). It involves only `Prime`, least prime factor
and Ω — **no analytic dependency**.

**Precise Lean statement** (proposed; imports
`Mathlib.NumberTheory.ArithmeticFunction.Liouville`, `Mathlib.Data.Nat.Prime.Basic`,
`Mathlib.Data.Nat.Factorization.Basic`; notation `Ω` from
`ArithmeticFunction.Omega`, `liouville` from `ArithmeticFunction`):

```lean
namespace Goldbach.Detector

/-- (Proposed B-017) Exact prime detector on cube-root-rough integers.
    `z` stands for any threshold with `N ≤ z^3`; `m < z^3` replaces `m < N`.
    `hrough` is `P^-(m) > z` expressed prime-by-prime. -/
theorem liouville_prime_detector_cuberough
    (z m : ℕ) (hz : 0 < z) (hm1 : 1 < m) (hmz : m < z ^ 3)
    (hrough : ∀ p, Nat.Prime p → p ∣ m → z < p) :
    (1 - liouville m) / 2 = if m.Prime then (1 : ℤ) else 0 := by
  -- proof sketch below
```

**Mathlib anchors already verified in source [SRC]:**
`Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean:27-31`
`liouville n = if n = 0 then 0 else (-1) ^ cardFactors n`,
`liouville_apply (h : n ≠ 0) : liouville n = (-1) ^ cardFactors n`;
`Misc.lean:258-267` `cardFactors n = n.primeFactorsList.length` with notation
`Ω`.

**Proof sketch (proposed, not verified):**
1. `hm0 : m ≠ 0` from `hm1`; rewrite `liouville m` via `liouville_apply hm0`
   and `cardFactors_apply`; let `L = m.primeFactorsList`.
2. Each `p ∈ L` is prime and divides `m` (`Nat.prime_of_mem_primeFactorsList`,
   `Nat.dvd_of_mem_primeFactorsList`), so `z < p` by `hrough`, hence `z + 1 ≤ p`.
3. Use `Nat.prod_primeFactorsList` (`m = L.prod id`, up to the exact Mathlib
   lemma name) to show `L.length ≤ 2`: if `L.length ≥ 3`, then
   `m ≥ (z+1)^3 > z^3`, contradicting `hmz`. With `1 < m`, get `1 ≤ Ω m ≤ 2`.
4. Case `Ω m = 1`: `L = [p]`, `m = p` prime; `liouville m = −1`; LHS `= 1`,
   RHS `= 1`. Case `Ω m = 2`: `L = [p,q]` with `p,q` primes `> z ≥ 1`;
   `m = p*q` is not prime (smallest factor `p > 1` divides `m` and `p ≠ m`),
   `liouville m = +1`; LHS `= 0`, RHS `= 0`. Close the `Int` division by
   `norm_num` once `liouville m` is pinned to `±1`.
5. Anticipated API checks at build time: exact lemmas for
   `primeFactorsList` membership/product, `Nat.Prime.not_prime_mul` (or
   `Nat.Prime.eq_one_or_self_of_dvd`), and `interval_cases`/`omega` for the
   length split. If those lemmas are missing, prove the two small supporting
   facts inline in the same file (AGENTS.md §3 "helpers in one file").

**Acceptance protocol if the parent adopts it:** exact theorem name present
(grep); build green; no `sorry`/`axiom`/`native_decide`/`admit`/`unsafe`/
`opaque`/`implemented_by`; `checker/strict_check.py` verdict pasted; only
`propext`/`Classical.choice`/`Quot.sound` in `#print axioms`; then flip status
in the map — **never** before the checker log says so. No git operations.

**Runner-up (not chosen):** the exact centering identity
`U_N = Σ_j (h⁺_j)² − Σ_j (h⁻_j)²` of `research.md:210` is also finite and
combinatorial and directly exposes the parity-energy obstruction, but it needs
a finite-sum/involution formalization over `Finset.range N`; the detector is
the smaller first step and is reused by both one-sided reductions.

---

## 4. Honest verdict: can ERH plausibly close the pointwise gap?

**Short answer [I]: Not by any route recorded in the repo — and the
parity/reflection obstruction survives as an obstruction to the specified
deductions. This is not a theorem that ERH cannot imply Goldbach; the answer
stays *open under ERH*.**

Evidence, all labelled:

1. **[Q]** `erh_attack.md:3`: "I obtain no proof that every even `N≥4` is a sum
   of two primes under the hypotheses in the question." **[Q]** `research.md:3`:
   "I find no proof that every even integer is the sum of two primes, even
   assuming Dirichlet GRH." **[Q]** `audit/REPO_AUDIT.md` C19: "Pointwise strong
   Goldbach remains open even under GRH" — explicitly "an honest limitation of
   the repo, not a theorem of independence" (line 77).

2. **The exceptional-set → pointwise gap is structural here [I].** The repo's
   kernel result is `E(X) ≤ 2·10⁶ √X log³X` (audit C18, CONDITIONAL) and
   `E(X)/X → 0`. Markov over dyadic blocks controls the *count* of exceptions;
   H1/H2/H3 each replace it with a **signed estimate at one frequency per even
   target**, and none of those signed inputs is established (§2.3). ERH gives
   the same pointwise zero-location as the repo's GRH; it does not supply the
   sign of the kernel (4).

3. **The same-sign zero-pair block survives ERH [Q/P].** GRH/ERH fixes
   `Re ρ = 1/2` but not cancellation in (4); the `T^{3/2}log²T` absolute
   magnitude and the surviving `N^{i(γ+γ')}` phases are computed *under* GRH
   (`research.md:100-118`). Audit B-011 remains `open`.

4. **The parity obstruction survives even stronger hypotheses [P].** The
   synthetic weights `a_n^± = K⁻¹w(n)(1±λ(n))` with `h(p)=1/(p−2)` satisfy the
   divisor tests `∑_{d|n} a_n^± = N/φ(d) + O(N^η(N/d)^{1/2+η})` to **every
   fixed level below 1** under RH, yet the plus sequence has **no primes**
   (`research.md:124-158`; audit C21 CONDITIONAL on RH Liouville estimate).
   The automorphic theorem (7) shows the prime-free model passes smoothed
   signed-difference GL_r tests at every level `<1` under automorphic RH +
   temperedness (`erh_attack.md:128-145`; audit C24). So even Grand RH-style
   tests of the specified kind are defeated.

5. **The Fourier/reflection holes survive [P].** In `ℤ/Mℤ`, a random half of
   each `±`-orbit has `(1_D*1_D)(0)=0` while all nonzero Fourier coefficients are
   `O(√(M log M))` (`research.md:182`; audit C22 UNVERIFIED construction); and
   on `N = 2^k` or `2p²` the largest-conductor reflection hole has all centred
   Fourier/character sums `O(√(N log N))` with the top family supplying exactly
   `−φ(N)` (audit C35). These are **tests of density and small individual
   coefficients, not models satisfying Dirichlet GRH** [Q, `research.md:182`].

6. **Auxiliary support/level obstructions survive ERH [P].** LWW's weight
   vanishes on every rough set (eq. (6)), the lower linear sieve dies at
   `z = N^{1/3}` (`s ≈ 3/2 ≤ 2`), and the one-sided routes need unestimated
   biases `H(N)`, `B_C(N)` (`erh_attack.md:105-198`).

7. **Crucial scope limit [Q/P].** `audit/REPO_AUDIT.md:344-346` cross-cutting
   blocker: "no single one of these is a theorem that GRH *cannot* imply
   Goldbach. The docs construct failures of specified deductions. Claiming
   logical independence would be speculation." A parity/reflection countermodel
   refutes a *deduction*, not the conjecture under ERH.

**Verdict:** ERH is not merely "unproved" — within the repo's framework it is
already *assumed* wherever "Dirichlet GRH" appears, and the framework still
has no pointwise result. The obstruction is a missing **two-input, signed**
estimate (off-diagonal `Λ(N−dk₁)Λ(N−dk₂)`, a two-form/dispersion step, or a
bias bound on the rough/Chen complement), which one-variable RH statements do
not provide. So: **pointwise Strong Goldbach is open under ERH; no `checked`
proof, no `checked` refutation; B-002 stays open.** The parity/reflection-hole
obstructions survive *as failures of the recorded routes*, and may also defeat
stronger automorphic hypotheses; that is evidence about proof strategies, not
independence.

---

## 5. What was actually done (no success claims)

- Read in full: `AGENTS.md`, `ARCHITECTURE.md`, `audit/REPO_AUDIT.md`,
  `goldbach-grh-lean/proof/strong_goldbach_erh_attack.md`,
  `goldbach-grh-lean/proof/strong_goldbach_research.md`; plus targeted reads of
  `map/blockers.json`, `proof/weak_goldbach_proof.md:1-12`, Mathlib/AINTLIB
  sources cited above.
- Commands: greps over repo and `/home/eequaled/lean-lake-cache/packages`;
  `mkdir -p /tmp/opencode/goldbach_erh`. **No Lean build, no checker run, no
  git operation, no map/desk/news/checker/lean file modification.**
- No arXiv PDF was fetched; all "supplied" papers are **[U] unverified**.
- Files written (sizes to be confirmed in the closing checkpoint):
  - `agents/CHECKPOINT_B-002.md` (created early, updated at close).
  - `audit/ERH_ROUTE_ANALYSIS.md` (this file).
- **No claim is made that Goldbach is true or false, nor that any theorem here
  is `checked`.** This is a research analysis plus one *proposed* blocker.
