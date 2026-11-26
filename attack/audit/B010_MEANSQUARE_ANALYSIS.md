# B-010 research analysis — the 1/4 mean-square exponent gap

**Date:** 2026-11-26. **Author:** subagent `agent-b010`. **Mode:** read-only research
analysis. **No proof of Goldbach, no status change, and no claim of `checked` is made.**

B-010 remains `open` in `map/blockers.json` as of the last read. Its recorded statement [Q,
`map/blockers.json`]: title "Close the 1/4 mean-square exponent gap (H1/H2 pointwise signed
minor-arc estimate)", why "L2 error gives single-coefficient allowance ~40N^(5/4)L^(3/2) but
positivity needs ~N: exponent gap exactly 1/4. Markov controls counts, not sign at a fixed
even N."

### Lease note (honest, required by delegation)

The delegated command `python3 desk/desk.py next --holder agent-b010 --program analytic --hard`
returned **B-004**, not B-010. Cause [I]: `desk.py cmd_next` sorts candidates by
`difficulty_rank` descending with a *stable* sort on ties (lines 323-324); B-004 and B-010 are
both `difficulty: "research"` (rank 4), and B-004 precedes B-010 in `map/blockers.json`, so
`--hard` deterministically selects B-004. `next` has no flag to target a specific id. I
**released** that lease (`ca7269cd4ab54041816852c36c00e8cb`, reason `wrong_blocker: ...`
targets B-010); the desk confirmed `"status": "released"`. Because this task is a read-only
analysis (no proof to submit), it does not require a held lease. **No B-010 lease is held.**
No desk state was touched except the `next`/`release` CLI calls.

### Label convention (applies to every claim below)

| Tag | Meaning |
|---|---|
| **[Q]** | Quoted (verbatim or near-verbatim, with line reference) from a repo file. |
| **[P]** | Paraphrased from a repo file; line reference given. |
| **[I]** | My inference / standard mathematical knowledge / my arithmetic; **not** established by the repo. |
| **[U]** | "Supplied" paper cited in a repo doc but whose PDF is **not** in the repo; unverified. |

Nothing in this document is `checked` under AGENTS.md §0: no Lean build was run here, and
`audit/REPO_AUDIT.md` §1/§3 already records that no repo theorem is kernel-checked. All
conditional statements stay conditional. All arithmetic below was checked by me with exact
integer/rational computation (Python `int`/`fractions.Fraction`), not by Lean.

---

## 1. The mean-square inequality, stated precisely; origin of 1600 and N^{5/2}L³

### 1.1 The quoted statement [Q]

`goldbach-grh-lean/proof/strong_goldbach_research.md:98` (Attack 1), verbatim key clauses:

> "In the companion binary proof's larger Farey dissection, let $E_n=\widehat{S^2-M^2}(n)$. Its
> GRH estimate is $\sum_{n\ge1}|E_n|^2\le1600N^{5/2}L^3$ at scale $X=N$."
> "Over a block of order $N$ integers it gives root-mean-square size $O(N^{3/4}L^{3/2})$."
> "For a *specified* coefficient its entire allowance is $40N^{5/4}L^{3/2}$."
> "Compared with a fixed positive multiple of $N$ the exponent gap for this deduction is
> **exactly $1/4$**, plus logarithms. An isolated negative error of size $N$ consumes just
> $N^2$ of the squared budget. This is a diagnosis of that theorem, not a lower bound on the
> actual error or on losses in every circle method."

So the object bounded is the Fourier coefficient of $S^2-M^2$ (notation $R_2(n)-M_2(n)$ in the
companion proof [Q, `binary_goldbach_exceptional_proof.md:27`]). $L=\log N$ [Q, companion
`:11` defines $L=\log X$; research doc uses scale $X=N$]. The inequality is a **GRH-conditional,
doc-stated** estimate; it is not machine-checked here ([I], cf. audit C18 CONDITIONAL).

### 1.2 Where the constant and exponents come from [Q] + [I]

The companion proof, `goldbach-grh-lean/proof/binary_goldbach_exceptional_proof.md`, Lemma 1
(lines 27-31), derives the identical bound at scale $X$:

- **[Q, lines 11, 14]** $D_2 := 20X^{-1/4}L$, and the arc approximation satisfies
  $|S-M|\le X D_2 = 20 X^{3/4}L$. The exponent $3/4$ is $1 - 1/4$: the $X^{-1/4}$ factor is
  the Dyadic/Dirichlet-box loss coming from arc width $Q\approx\sqrt{2\pi X}$ ($H\approx\sqrt X$)
  and the major-arc denominator $\varphi(q)\gtrsim\sqrt q$ [P, lines 11, 25].
- **[Q, line 28]** Parseval: $\int_0^1|S|^2\le1.039X(L/2+1)$.
- **[Q, line 29]** $\int_0^1|M|^2\le Xe(1+\log H)/2$, and the two squared norms sum to $\le 2XL$.
- **[Q, lines 30-31]** Bessel + $|S+M|^2\le2(|S|^2+|M|^2)$ give
  $$\sum_{n\ge1}|R_2(n)-M_2(n)|^2\le\int_0^1|S^2-M^2|^2
  \le 2(XD_2)^2\int_0^1(|S|^2+|M|^2)\le1600X^{5/2}L^3.$$

**[I] Exact arithmetic (verified with Python integers):** the constant is the product of three
explicit factors:
$$1600 = \underbrace{2}_{|S+M|^2\le2(\cdot)}\cdot\underbrace{20^2}_{(XD_2)^2}\cdot\underbrace{2}_{\int|S|^2+\int|M|^2\le2XL} = 2\cdot400\cdot2.$$
The exponents: $(X^{3/4})^2\cdot X = X^{3/2+1}=X^{5/2}$; $L^2\cdot L = L^3$. Substituting
$X=N$ reproduces the research doc's $1600N^{5/2}L^3$. $\sqrt{1600}=40$, giving the doc's
specified-coefficient allowance $40N^{5/4}L^{3/2}$ [Q + I].

**[I] Independent cross-check of the downstream constant (exact arithmetic):** Lemma 6 [Q,
lines 63-67] marks $n$ bad when $|R_2-M_2|\ge X/16$ and bounds the count by
$1600X^{5/2}L^3/(X/16)^2 = 1600\cdot16^2\sqrt X L^3 = 409600\sqrt X L^3$ — the doc's
$409600$ [Q, line 66] matches. Lemma 7 sums over dyadic scales with factor
$(1-2^{-1/2})^{-1}<3.415$: $410000\cdot(1-2^{-1/2})^{-1}=1{,}399{,}827.56<2{,}000{,}000$
[Q, lines 71-73; I], consistent with the audited interval-verifier result
`global C ≤ 1399827.57 < 2,000,000` (audit command #9, claim C14). These checks confirm the
**internal arithmetic** of the doc chain; they do not check GRH, the explicit formula, or any
Lean elaboration.

### 1.3 Provenance label table

| Number | Label | Source |
|---|---|---|
| $\sum|E_n|^2\le1600N^{5/2}L^3$ | **[Q]** (doc), **[P]** (companion at $X$) | research.md:98; binary proof:31 |
| $1600=2\cdot20^2\cdot2$ | **[I]** exact re-derivation | binary proof:11,14,28-31 |
| $D_2=20X^{-1/4}L$, $|S-M|\le20X^{3/4}L$ | **[Q]** | binary proof:11,14,23 |
| $X^{5/2}L^3=(X^{3/4})^2\cdot X\cdot L^2\cdot L$ | **[I]** arithmetic | binary proof:30-31 |
| $40N^{5/4}L^{3/2}=\sqrt{1600N^{5/2}L^3}$ | **[Q]** value, **[I]** square root | research.md:98 |
| $409600=1600\cdot16^2$; $1{,}399{,}827.56<2\cdot10^6$ | **[Q]** values, **[I]** arithmetic | binary proof:66,72-73 |

---

## 2. Artifact of the L²+Markov method, or a genuine barrier?

### 2.1 The exponent arithmetic, done explicitly [I]

Let the mean-square bound be $\sum_{n\ge1}|E_n|^2\le C N^{\alpha}$ (suppress logarithms;
$C=1600$, $\alpha=5/2$ in the quoted case). At scale $N$, the relevant Fourier coefficients
are indexed by an interval of order $N$ integers, so the number of coefficients is
$M\asymp N$ [Q "block of order $N$ integers", research.md:98; I].

Two deductions are possible, and they are *not* interchangeable:

**(A) Sup norm / a specified coefficient (Cauchy–Schwarz).** Since every term is nonnegative,
$$|E_{n_0}|^2\le\sum_{n\ge1}|E_n|^2\le C N^{\alpha}\quad\Longrightarrow\quad |E_{n_0}|\le\sqrt C\,N^{\alpha/2}.$$
For $\alpha=5/2$ this is $\sqrt{1600}\,N^{5/4}=40N^{5/4}$ (times $L^{3/2}$): the doc's
"entire allowance" [Q]. Compare to the required order $N$ (a fixed positive multiple of $N$):
the exponent is $5/4$ versus $1$, so the **sup-norm exponent gap is $5/4-1=1/4$** [Q+I].
For this deduction to give $|E_{n_0}|=o(N)$ one needs $\alpha/2<1$, i.e.
$$\boxed{\alpha<2\quad\text{(equivalently }\sum|E_n|^2\ll N^{2-\varepsilon}\text{)}}.$$
To get merely $O(N)$ one needs $\alpha\le2$ (with the constant then having to beat the
positivity margin, e.g. $1.32032/(2e)-3/16-1/100>0.045$ [Q, binary proof:93]).
Thus in the **mean-square exponent** the required saving from the quoted $5/2$ is more than
$1/2$; in the **single-coefficient exponent** it is $1/4$. Both are the same statement viewed
at different levels.

**(B) RMS over a block (typical coefficient).** Averaging over $M\asymp N$ coefficients,
$$\text{RMS}=\sqrt{\frac{C N^\alpha}{M}}\asymp\sqrt C\,N^{(\alpha-1)/2}
=N^{(5/2-1)/2}=N^{3/4}\ (\text{times }L^{3/2}),$$
matching the doc's $O(N^{3/4}L^{3/2})$ [Q, research.md:98; I]. Since $3/4<1$, the RMS is
already $o(N)$; the *average* coefficient is harmless. The task's formula
$N^{\alpha/2}/\sqrt{\#\text{coefficients}}$ is exactly this with $\#\approx N$.

### 2.2 Why (B) does not help a specified target, and why the gap is structural to this deduction

The target in H1/H2 is a **single specified even $N$** [Q, research.md:61-95; audit C20].
Deduction (B) is a statement about the average; nothing in Bessel/Parseval prevents one
coefficient from carrying the whole budget, so a specified $n_0$ must be bounded by (A), not
(B). Quantitatively, Markov gives
$$\#\{n:|E_n|\ge T\}\le \frac{C N^{5/2}L^3}{T^2}.$$
Setting $T=\delta N$ gives at most $C\delta^{-2}N^{1/2}L^3$ exceptions — this is precisely the
exceptional-set bound $E(X)\le2\cdot10^6\sqrt X\log^3X$ [Q, binary proof:4; audit C18], now seen
as the Markov shadow of the mean square. It is a **density-one** statement, not a pointwise one.

An isolated negative error of magnitude $N$ at the target consumes $N^2$ of the budget
$N^{5/2}L^3$, i.e. a fraction $1/(1600\,N^{1/2}L^3)\to0$ [Q "consumes just $N^2$",
research.md:98; I]. Hence the mean-square bound is fully compatible with *many*
(size up to $N^{5/4}L^{3/2}$) outliers, including a single one at the target. **The mean-square
bound cannot, by itself, decide the sign at a fixed even $N$.**

### 2.3 Verdict on "artifact vs barrier" [Q + I]

- **[Q]** The repo itself labels this a "diagnosis of that theorem, not a lower bound on the
  actual error or on losses in every circle method" (research.md:98). So the repo does **not**
  assert that the true error is anywhere near $N^{5/4}$.
- **[I]** The $1/4$ is an artifact of the *combination* of (i) a pointwise error
  $|S-M|\le20X^{3/4}L$, (ii) squaring, and (iii) replacing a specified coefficient by the
  Cauchy–Schwarz sup. Any one of these could in principle be improved: a better pointwise
  error (e.g. $\ll X^{1/2+\varepsilon}$), a higher-moment bound with $\alpha<2$, or a signed
  (not absolute) estimate at the target would remove the exponent gap. It is therefore **not a
  proved barrier** to all circle-method approaches.
- **[Q]** But it *is* a real barrier to the recorded exceptional-set $\to$ pointwise deduction:
  "An isolated negative error of size $N$ consumes just $N^2$ of the squared budget", and
  "the exceptional-set theorem applies to a different model from (H1); one cannot substitute
  its average for (H1)" (research.md:98). Replacing the mean square by the "supplied quasi-RH
  fourth-moment exceptional count still permits an isolated exception" **[Q, same line]**.
- **[I]** Higher moments do not fix this in general: for any fixed finite moment
  $\sum|E_n|^p\le N^{\beta}$, Cauchy–Schwarz/Hölder still gives a single coefficient
  $\le N^{\beta/p}$, and an isolated outlier of size $N$ costs only $N^p$ against a budget
  growing faster. Only a bound in which the *whole budget* is below $N^2$ (i.e. $\alpha<2$
  at $p=2$) or a genuinely signed input at the target can close it. This matches the repo's
  route note for B-010: "Pointwise signed minor-arc estimate; higher-moment/quasi-RH
  exceptional counts (may still allow isolated exceptions)" [Q, `map/blockers.json` B-010.route].

**Conclusion [I]:** within the *recorded* method the gap is structural (Markov controls counts,
not sign); it is **not** a theorem that the true error has exponent $5/4$, nor that Goldbach
is unprovable under GRH/ERH. The answer stays open.

---

## 3. One concrete, checkable micro-step (proposed, unverified)

### 3.1 Choice — [I]

Of the three candidates, **(b) "a pure Cauchy–Schwarz / Markov lemma in Lean"** is the most
tractable and the one that most directly formalises the logical step at issue. Candidate (a)
(recompute 1600) was already carried out above in §1.2 with exact arithmetic — it confirms the
constant is *not* the problem (the exponent is), but it does not advance the blocker further.
Candidate (c) (numerical mean-square estimate for a test function) would only tell us about a
model, not about $S^2-M^2$, and would not be a Lean-checkable step. So I write up (b).

**Status: PROPOSED / UNVERIFIED — not written to `lean/`, not built, not added to `map/`.**

### 3.2 Precise Lean statement (proposed)

The logical kernel of §2.1(A) is: a nonnegative finite sum bounds each of its terms. This is a
pure order/finset fact with no analysis dependency. Mathlib anchor [SRC, source-level, not
built]: `Finset.single_le_sum`, signature
`(∀ b ∈ s, 0 ≤ f b) → a ∈ s → f a ≤ ∑ b ∈ s, f b`; precedent at
`Mathlib/Algebra/Polynomial/UnitTrinomial.lean:194`:
`single_le_sum (fun k _ => sq_nonneg (p.coeff k)) hk`.

```lean
namespace Goldbach.B010

/-- (Proposed B-010 micro-step) Cauchy-Schwarz sup bound: a nonnegative mean-square
    budget bounds every individual squared coefficient. Pure finset/order; no analysis. -/
lemma sq_coeff_le_sum_of_l2_budget
    {ι : Type*} [Fintype ι] (E : ι → ℝ) (B : ℝ)
    (hbudget : ∑ i, (E i) ^ 2 ≤ B) (i0 : ι) :
    (E i0) ^ 2 ≤ B := by
  exact (Finset.single_le_sum (fun j _ => sq_nonneg (E j)) (Finset.mem_univ i0)).trans hbudget

/-- (Proposed, companion) The same budget bounds the *minimum* by the RMS: if the budget
    is C*N^alpha and there are M ~ N coefficients, then min |E_i| <= sqrt(C)*N^((alpha-1)/2).
    Stated without sqrt/analysis as: M * min_i (E i)^2 <= sum <= B. -/
lemma card_mul_min_sq_le_sum
    {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (B : ℝ)
    (hbudget : ∑ i, (E i) ^ 2 ≤ B) :
    Fintype.card ι * (⨅ i, (E i) ^ 2) ≤ B := by
  -- proof sketch: sInf_le each term => (⨅ i, E i^2) <= E j^2; sum over j gives
  -- card * iInf <= sum via Finset.sum_const / Finset.sum_le_sum; trans hbudget.
  sorry -- PLACEHOLDER: not proved here, proposed only

end Goldbach.B010
```

**Proof of the first lemma (complete, in sketch above):** `Finset.single_le_sum` with
`sq_nonneg` gives `(E i0)^2 ≤ ∑ i, (E i)^2`; `.trans hbudget` closes. No `sorry` is needed
for this lemma. The second lemma's `sorry` marker is explicitly a **proposal placeholder**,
not a submitted proof; it would be filled with `Finset.sum_le_sum` + `Finset.sum_const` at
build time, with exact lemma names confirmed then (AGENTS.md §3 "helpers in one file").

**Acceptance protocol if the parent adopts it [I]:** exact theorem names present (grep); green
build; no `sorry`/`axiom`/`native_decide`/`admit`/`unsafe`/`opaque`/`implemented_by` tokens in
the final file; `checker/strict_check.py` verdict pasted; `#print axioms` shows only
`propext`/`Classical.choice`/`Quot.sound`; flip map status only after the checker log says so.
No git operations. **This lemma formalises the deduction; it does not close the 1/4 gap** — it
makes explicit that a mean-square budget alone yields only a sup bound $N^{\alpha/2}$, so it
*locates* exactly where a signed input is required.

---

## 4. Honest verdict: can the gap be closed with known techniques?

**Short answer [I]: Not by any route recorded in the repo. The repo does not claim a solution,
and we make none. Pointwise Strong Goldbach stays open under GRH/ERH.**

Evidence, all labelled:

1. **[Q]** research.md:3: "I find no proof that every even integer is the sum of two primes,
   even assuming Dirichlet GRH." **[Q]** research.md:98: "This is a diagnosis of that theorem,
   not a lower bound on the actual error." Audit C19: pointwise strong Goldbach remains open
   even under GRH — "an honest limitation of the repo, not a theorem of independence" [Q,
   REPO_AUDIT.md:77].
2. **[Q + I]** The mean-square $\to$ pointwise step loses exactly $1/4$ in the coefficient
   exponent (§2.1), and an isolated size-$N$ outlier is nearly free within the budget (§2.2).
   Markov gives density one, not sign at a fixed target — this is B-010's own `why` field [Q].
3. **[Q]** Replacing the mean square with the quasi-RH fourth-moment exceptional count "still
   permits an isolated exception" (research.md:98), and the exceptional-set theorem "applies to
   a different model from (H1)" [Q]. The repo's H1/H2/H3 reductions (audit C20) are conditional
   on **unproved** signed inputs — none established.
4. **[I]** In principle a stronger pointwise error ($\ll X^{1/2+\varepsilon}$), a mean-square
   exponent $<2$, or a signed minor-arc estimate at the target would close the *exponent*
   gap; these are exactly the unproved directions. The repo's own B-010 route is a "pointwise
   signed minor-arc estimate" [Q, blockers.json]. No such estimate is supplied or proved here.
5. **[Q, REPO_AUDIT.md:344-346]** Cross-cutting limit: "no single one of these is a theorem
   that GRH *cannot* imply Goldbach. The docs construct failures of specified deductions.
   Claiming logical independence would be speculation." So this analysis is evidence about a
   proof strategy, **not** an independence result.

**Verdict:** B-010 stays `open`. No `checked` proof and no `checked` refutation. The 1/4 is a
sharp diagnosis of the exceptional-set method's passage from an $L^2$ bound to a single
coefficient, not a proven lower bound and not an unconditional obstruction. Closing it needs a
signed, pointwise input that the repo explicitly does not have.

---

## 5. What was actually done (no success claims)

- **Read in full:** `AGENTS.md`, `ARCHITECTURE.md`, `audit/REPO_AUDIT.md`,
  `audit/ERH_ROUTE_ANALYSIS.md`; targeted reads of
  `goldbach-grh-lean/proof/strong_goldbach_research.md` §2 (line 98) and
  `goldbach-grh-lean/proof/binary_goldbach_exceptional_proof.md` (lines 1-94), plus
  `map/blockers.json` B-010 record and `desk/desk.py` selection logic (lines 206-335).
- **Commands:** the delegated `desk.py next` (returned B-004), `desk.py release` (of B-004),
  exact integer/rational arithmetic in Python, and source greps for Mathlib lemma anchors.
  **No Lean build, no checker run, no git operation, no arXiv fetch, and no modification of
  `map/`, `lean/`, `desk/` (beyond CLI), `checker/`, `news/`, or the cloned repo.**
- **Files written:** `agents/CHECKPOINT_B-010.md` and this file
  `audit/B010_MEANSQUARE_ANALYSIS.md`. (Final byte sizes recorded in the checkpoint at close.)
- **No claim** is made that Goldbach is true or false, that any theorem here is `checked`, or
  that the 1/4 gap has been closed. The Lean lemma in §3 is **proposed/unverified**.

---

## Lease and status

- **Lease id:** `7b36610883284b4d9ea93cbf2b1d64f1` (blocker **B-010**, holder `agent-b010`,
  obtained with `python3 desk/desk.py next --holder agent-b010 --id B-010`).
- **Status [Q, `map/blockers.json`]:** B-010 is `open` and **unresolved** — the 1/4 mean-square
  exponent gap is not closed; no `checked` proof and no `checked` refutation exists.
- **Nature of this work:** this document is a **read-only research analysis**. No proof is
  claimed, no theorem is asserted `checked`, no status was changed in `map/`, and no Lean,
  git, checker, news, or cloned-repo file was modified. The only file written in this follow-up
  is this analysis (plus the checkpoint, written in the earlier session). The lease is released
  at the end with reason `analysis_complete_no_proof`.
