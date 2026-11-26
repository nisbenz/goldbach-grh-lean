# Honest audit of `goldbach-grh-lean`

Audited: 2026-11-26. Auditor subagent. Workspace `/home/eequaled/goldbach`;
cloned repo `/home/eequaled/goldbach/goldbach-grh-lean` (also symlinked at
`refs/goldbach-grh-lean`). The cloned repo was **not modified** and **no git
operations** were run in it. Build artifacts were confined to
`/tmp/opencode/goldbach_audit/lean_build` (a byte-for-byte scratch copy of
`lean/`). Companion machine-readable inventory: `audit/claim_inventory.json`.

Status vocabulary (this audit): **CHECKED** = a command was run and observed to
succeed, or a source-level fact was directly read; **CONDITIONAL** = the statement
is explicitly proved only under named hypotheses (GRH/ERH/etc.) or by postulating
a named unproved input; **UNVERIFIED** = no machine check was completed (this
includes every Lean elaboration claim, because no `lake build` succeeded here);
**REFUTED** = directly contradicted by source/evidence. A result being
"CONDITIONAL" never means "checked under that hypothesis" unless a kernel build
actually ran.

---

## 1. Commands actually run (with exits and last lines)

| # | Command (working directory) | Exit | Observed last lines / result |
|---|---|---:|---|
| 1 | `export PATH="$HOME/.elan/bin:$PATH"; elan show` (workspace) | 0 | Preinstalled: `v4.33.1`, `v4.34.0`, `v4.34.1 (default)`, `v4.36.0`. **v4.16.0 absent.** |
| 2 | `elan toolchain install leanprover/lean4:v4.16.0` | 0 | `leanprover/lean4:v4.16.0 installed - Lean (version 4.16.0, commit 128a1e6b0a82, Release)` (~1 min; within 15-min budget) |
| 3 | `cp -a .../goldbach-grh-lean/lean /tmp/opencode/goldbach_audit/lean_build` then `lake --version` (scratch) | 0 | `Lake version 5.0.0-128a1e6 (Lean version 4.16.0)` |
| 4 | `timeout 300 lake exe cache get` (scratch) | **124** | No output; `.lake/packages/` empty. Mathlib cache not obtained. |
| 5 | `timeout 90 lake -v exe cache get` (scratch, retry) | **124** | No output; still no packages. |
| 6 | `lake build` | **not run** | Per instruction: only attempt if v4.16.0 installed *and* mathlib cache obtainable quickly. Cache failed twice, so no build. |
| 7 | `grep -rniI --include='*.lean'` for `sorry\|axiom\|native_decide\|unsafe\|admit\|opaque\|implemented_by\|sorryAx` (repo `lean/`) | 0 | 4 `sorry` **tokens, all in comments**; 17 real `axiom` declarations; zero `native_decide`, `unsafe`, `admit`, `opaque`, `implemented_by`, `sorryAx`. `#print axioms` appears at `Main.lean:40`, `BinaryExceptional.lean:274-275`. |
| 8 | `python3 verify/verify_bounds.py` (repo root) | 0 | `ALL ANALYTIC CONSTANTS AND INEQUALITIES VERIFIED WITH RIGOROUS INTERVAL BOUNDS!` (all `[PASS]`; e.g. net strictly-prime coefficient/X² ≥ 0.08785644 > 0.083) |
| 9 | `python3 verify/verify_binary_bounds.py` (repo root) | 0 | `ALL BINARY GOLDBACH EXCEPTIONAL-SET CONSTANTS AND INEQUALITIES VERIFIED!` (all `[PASS]`; global C ≤ 1399827.57 < 2,000,000) |
| 10 | `g++ -O3 -std=c++17 -pthread verify/verify_finite.cpp -o /tmp/opencode/goldbach_audit/verify_finite` | 0 | Produced 23,560-byte executable. **Not executed** (1e9 sieve / 1e12 ladder = hours). |
| 11 | `python3 /tmp/opencode/goldbach_audit/check_ladder.py` (reads `verify/ladder_certs.json.gz`) | 0 | `rungs 2501`, `p0 3999999999999999887`, `p_last 10003999999999999876777`, gaps/max-step constraints OK, `all_rung_certs_verified True`, `unique_primes_verified 13197`, 0.33 s. |
| 12 | `timeout 15 curl -sSI https://github.com/leanprover-community/mathlib4` | 0 | `HTTP/2 200` (GitHub reachable; the stall is in Lake's fetch/cache step, not generic DNS) |
| 13 | `timeout 15 curl -sSI https://matlib.cmu.edu` | 6 | `Could not resolve host: matlib.cmu.edu` |

File inventory (bytes, from `find ... -printf`): `README.md` 5,408;
`lean/lean-toolchain` 24; `lean/lakefile.toml` 218; `lean/lake-manifest.json` 3,118;
`lean/WeakGoldbach.lean` 217; `Defs.lean` 1,619; `PrimeLadder.lean` 3,889;
`Pratt.lean` 5,290; `Analytic.lean` 23,673; `Main.lean` 1,951;
`BinaryExceptionalCore.lean` 12,093; `BinaryExceptional.lean` 14,085;
`proof/weak_goldbach_proof.md` 14,613; `proof/binary_goldbach_exceptional_proof.md` 10,881;
`proof/strong_goldbach_research.md` 28,700; `proof/strong_goldbach_erh_attack.md` 29,096;
`proof/strong_goldbach_nov2026_ratios_attack.md` 40,398;
`proof/strong_goldbach_persistent_push.md` 48,430;
`verify/verify_bounds.py` 14,457; `verify/verify_binary_bounds.py` 6,088;
`verify/verify_ladder.py` 7,319; `verify/verify_finite.cpp` 8,499;
`verify/ladder_certs.json.gz` 830,228 (sha256 `6df1b268…c76cbb6e78a1`).
`README.md` sha256 `719bb42a…ba20b077200`; `Main.lean` sha256 `037a9d33…d2c1f275fdc072b4ba80a00`.

---

## 2. Claims table

| ID | Claim (short, as stated in repo) | Status | Evidence (command + exit, or "not run") | Caveat |
|---|---|---|---|---|
| C01 | Lean pinned to `leanprover/lean4:v4.16.0` + Mathlib `v4.16.0` (`rev a6276f4c…`) | CHECKED | Read `lean/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`; `lake --version` = 4.16.0 in scratch | Manifest pins 8 packages incl. inherited deps at assorted revs. |
| C02 | "zero `sorry`s" | CHECKED | Grep #7: 4 `sorry` tokens, all in comments; 0 code occurrences | Literal token claim only; says nothing about axioms. |
| C03 | "zero axioms" / "zero-axiom" (comments in `Analytic.lean:45,63,272`, `BinaryExceptionalCore.lean:117,200`, `BinaryExceptional.lean:97`, `Main.lean:…) | **REFUTED** | Grep #7: 17 `axiom` declarations (§3) | At most true of *selected helper lemmas*; false of every final theorem. |
| C04 | `lake build` passes with zero sorries and a `#print axioms` audit | **UNVERIFIED** | Commands #4/#5 exit 124; command #6 not run | No build output observed; cannot assert elaboration of any theorem. |
| C05 | `#print axioms <final theorem>` shows only `propext`, `Classical.choice`, `Quot.sound` | **UNVERIFIED** | Static: 3 print statements found, no output seen | Static axiom declarations guarantee custom names would be printed if a build ran. |
| C06 | `threshold_inequality : ∀ N ≥ 10²², coeff > 0.083` is kernel-verified over ℝ | UNVERIFIED | Source read (`Analytic.lean:275-419`); no build | Lemma itself declares no new axiom, but not elaborated here. |
| C07 | `isSumOfThreePrimes_of_R_prime_pos` (positivity ⇒ ternary representation) | UNVERIFIED | Source read (`Analytic.lean:46-58`); no build | A finite sum argument, axiom-free in source. |
| C08 | Pratt soundness `prime_of_lucas_trace` is zero-axiom | UNVERIFIED | Source read (`Pratt.lean:77-111`), uses Mathlib `lucas_primality`; no build | Soundness of the *Python-generated certificates* is separate from the Lean theorem. |
| C09 | `weakGoldbach_complete` glues binary-up-to-B + ladder + analytic ⇒ full Weak Goldbach | UNVERIFIED | Source read (`PrimeLadder.lean:80-87`); no build | It is an implication theorem; assumptions are axioms in `Main.lean`. |
| C10 | `weak_goldbach_theorem : WeakGoldbachConjecture` (all odd N≥7) | UNVERIFIED + CONDITIONAL on axioms | Source read (`Main.lean:33-38`); no build | **Not conditional on GRH as a Lean hypothesis.** GRH appears only in comments justifying axioms. Kernel would see 3+ axioms. |
| C11 | Kernel `dyadic_exceptional_bound`, `binary_goldbach_exceptional_bound`, `binary_goldbach_density_one` | UNVERIFIED + CONDITIONAL | Source read (`BinaryExceptional.lean:100,245,269`); no build | Depend on `binaryGoldbach_4e18` + 10 analytic axioms (§3). |
| C12 | `global_bound_of_dyadic_sqrt_log`, `density_one_of_sqrt_log_bound` are axiom-free combinatorial/analytic lemmas | UNVERIFIED (source-level supported) | Source read (`BinaryExceptionalCore.lean:121,203`); no build | Source declares no axioms; Mathlib axioms (`propext`, quotient, choice) still expected. |
| C13 | 60-digit verifier of every weak-proof constant/inequality (`verify_bounds.py`) | CHECKED (execution) | Command #8 exit 0; all `[PASS]` | Checks **arithmetic inequalities**, not GRH, not explicit formulae, not Lean. Some parametric checks use 53-bit `float` grids (`check_lemma1` uses `math`/`float`), so "every constant with rigorous intervals" is overstated. |
| C14 | 60-digit verifier of every binary-proof constant/inequality (`verify_binary_bounds.py`) | CHECKED (execution) | Command #9 exit 0; all `[PASS]` | Same scope caveat: hardcoded analytic inputs assumed; no proof of Lemmas 1–5. |
| C15 | `verify_finite.cpp` compiles | CHECKED | Command #10 exit 0 | Compile only. **The 1e9/1e12 run was not performed**; no "PASS: Checked …" observed. |
| C16 | Ladder: 2,501 rungs, 13,197 unique Pratt-certified primes, B=4e18→N0=1e22, max gap B−4 | CHECKED | Command #11 exit 0, independent recursive Pratt check in scratch (0.33 s) | Verifies certificates and ladder constraints only; does **not** verify binary Goldbach up to 4e18, and my checker reuses the same Pratt criterion as the repo's Python (not a Lean check). |
| C17 | Proof: every odd N≥10²² is a sum of 3 primes under GRH (incl. zeta) | CONDITIONAL (GRH) | Read `proof/weak_goldbach_proof.md`; not machine-checked | Also assumes BMOR/Backlund/Rosser–Schoenfeld numeric inputs as stated; uses finite ladder from external literature. |
| C18 | Proof: E(X) ≤ 2,000,000√X log³X for X≥4 under GRH; density one | CONDITIONAL (GRH) | Read `proof/binary_goldbach_exceptional_proof.md`; not machine-checked | Uses finite verification through 4e18 and companion Lemma 3 product certificate. |
| C19 | Pointwise strong Goldbach remains open even under GRH | CHECKED (repo's own conclusion) | `README.md:8`, `strong_goldbach_research.md:3,212-214`, `persistent_push.md:326-331` all state no proof | This is an honest limitation of the repo, not a theorem of independence. |
| C20 | H1/H2/H3 one-sided reductions reach the finite endpoint C=4e18 | CONDITIONAL (RH/GRH + H1/H2/H3 + finite verification) | Read `strong_goldbach_research.md:24-44,84-95,197-208` | H1/H2/H3 are explicitly **unproved** negative-correlation bounds; not Lean-checked. |
| C21 | Parity countermodel passes divisor tests at every fixed level <1 and has no primes | CONDITIONAL (RH Liouville estimate) | Read `strong_goldbach_research.md:124-158`; not machine-checked | Countermodel to a * deduction*, not a GRH countermodel. |
| C22 | Fourier reflection-hole counterexample (Z/MZ) with small individual coefficients | UNVERIFIED (mathematical argument read, not re-derived) | Read `strong_goldbach_research.md:182`, `persistent_push.md:305-322` | Probabilistic finite construction; no code run. |
| C23 | Smooth reflected d₂,d₂ sum has pointwise O_ε(N^{3/4+ε}) unconditionally | UNVERIFIED | Read `erh_attack.md:37-71` | Claimed unconditional via Voronoi+Weil; not independently checked. |
| C24 | Automorphic-RH parity survival theorem (7) | CONDITIONAL (automorphic RH, temperedness, Lindelöf, finite-place Ramanujan) | Read `erh_attack.md:128-145` | Model passes GL_r tests; does not transfer to primes. |
| C25 | Subcritical z=N^{2/9} marked-divisor reduction (8) | CONDITIONAL (GRH + bias inequality for H(N)) | Read `erh_attack.md:149-184` | H(N) unestimated; LWW weights vanish on that rough set. |
| C26 | Chen-set one-sided reduction (9) | CONDITIONAL (quantitative Chen + Möbius bias B_C(N)) | Read `erh_attack.md:186-198` | No explicit c or N₀ derived; no finite bridge. |
| C27 | GWX ratios route gives G(N)=N𝔖(N)+O(N^{1−ω_D+ε}) | CONDITIONAL (GWX Hypothesis 1.1; supplied arXiv:2611.18825v1) | Read `ratios_attack.md:7-18` | Repo itself does not prove GWX; no local PDF in repo. |
| C28 | Dirichlet ratios error O_{η,ε}(q^{−η+ε}) via joint product cutoff | CONDITIONAL (Dirichlet GRH, fixed small η, smooth mollifiers) | Read `ratios_attack.md:92-94` | Exponent optimum of that method; still η short of detector need. |
| C29 | Direct signed moment reaches critical exponent B_q(η) ≪ q^{1−2η+ε} | CONDITIONAL (GRH) | Read `ratios_attack.md:170-191` | Model itself has size ≍p^{1−2η}; triangle bound cannot give o. |
| C30 | Moving-line criterion B_q(c/log 2q)=o(φ*(q)) ⇒ asymptotic Goldbach | CONDITIONAL (the criterion itself + GRH) | Read `ratios_attack.md:154-168` | Not established; asymptotic ⇒ all-even needs finite bridge. |
| C31 | Pascadi Selberg exponent 8/15 (height aspect); 0.532 twisting length | CONDITIONAL (Selberg; supplied arXiv:2611.34917v1) | Read `persistent_push.md:82-101`, `ratios_attack.md:3,104` | Not a conductor-aspect endpoint; no local PDF. |
| C32 | Li–Liu narrowing to a=1.8999998 uncond / a=1.39998 under WEH(0.999) | CONDITIONAL (WEH(0.999) for second; continuity bound for first) | Read `persistent_push.md:230-271`, cited arXiv:2606.05224v2 | Cannot reach a=1: divergence as b↓1; supplied statements only. |
| C33 | Exact GWX-model subtraction identity (2) at fixed conductor | CONDITIONAL (Dirichlet GRH) | Read `persistent_push.md:35-58` | Residual is the unknown signed prime-pair vs singular-series difference; no estimate. |
| C34 | Positive-definite sum-kernel detector is impossible; N=8 exact negative sign example | UNVERIFIED (argument read) | Read `persistent_push.md:180-209` | Obstruction to a proof strategy, not to Goldbach. |
| C35 | Sparse-conductor reflection hole at 2^k and 2p² | UNVERIFIED (construction read) | Read `persistent_push.md:305-322` | Artificial model; explicitly not a GRH/GWX-satisfying model. |

---

## 3. The axiom audit (the central finding)

The README advertises "`sorry`-free Lean 4 formalizations" (true) and the Lean
comments repeatedly say "zero axioms". Source-level grep finds **17 declared
`axiom`s**, i.e. new, unproven constants in the kernel sense:

* `lean/WeakGoldbach/Analytic.lean` (5):
  `R_total`, `M_coeff` (430–431 — bare functions ℕ→ℝ, no properties),
  `grh_arc_error_bound` (437), `major_arc_main_term_lower_bound` (445),
  `prime_power_subtraction_bound` (454). None takes GRH as a Lean hypothesis;
  "under GRH" is only the informal provenance in a comment (421–426).
* `lean/WeakGoldbach/BinaryExceptional.lean` (10):
  `R2_total`, `M2_coeff`, `T_trunc`, `U_tail`, `S2_series`, `J_int` (33–38),
  `grh_binary_arc_L2_bound` (43), `binary_singular_integral_bounds` (51),
  `binary_singular_series_bounds` (61), `binary_prime_power_bound` (73).
* `lean/WeakGoldbach/Main.lean` (2):
  `binaryGoldbach_4e18 : BinaryGoldbachUpto (4*10^18)` (15) and
  `certified_prime_ladder_1e22 : PrimeLadder B_verified N0` (23).

Consequences:

1. `weak_goldbach_theorem` is a theorem of a theory containing GRH-derived
   *axioms*, a 4e18 finite-computation *axiom*, and a ladder *axiom* — not a
   theorem of Lean/Mathlib alone and not a theorem with a `GRH` hypothesis you
   can inspect. Calling it "GRH-conditional" is fair informally but the formal
   statement has **no hypothesis at all**; its axiom list is the hypothesis.
2. `binary_goldbach_exceptional_bound` and `binary_goldbach_density_one`
   likewise depend on `binaryGoldbach_4e18` plus ten analytic axioms. The
   genuinely axiom-free (in source) parts are `BinaryExceptionalCore.lean`'s
   Chebyshev/Markov/dyadic/density lemmas, the threshold inequality, Pratt
   soundness, and the ladder gluing.
3. `#print axioms` commands are present, but since no build ran, **no printed
   axiom list was observed**. Under AGENTS.md §0, these theorems would not be
   `checked`: they have new axioms beyond `propext`/`Classical.choice`/`Quot.sound`.
4. The Python verifier runs do not repair this: they check numbers appearing in
   the prose proofs, and the C++ compile does not connect to `binaryGoldbach_4e18`.

This is the single most important correction to the README's framing. It is not
evidence that the proofs are wrong — only that the claimed kernel status is
overstated and unverified here.

---

## 4. What is genuinely verified vs claimed-but-unverified

**Genuinely verified in this audit (observed outputs):**

* Toolchain pin and dependency manifest read; v4.16.0 install succeeded.
* Zero `sorry`/`admit`/`native_decide`/`unsafe`/`opaque`/`implemented_by` tokens in Lean code.
* 17 axiom declarations counted and listed (§3).
* Both Python interval verifiers execute to exit 0 with all `[PASS]` lines; they
  establish the stated numerical inequalities under their hard-coded inputs.
* C++ verifier compiles cleanly with the documented flags.
* The gzipped ladder data really contains 2,501 rungs/13,197 distinct primes,
  endpoints and gap constraints as advertised, and every recursive Pratt
  certificate validates under an independent Python re-check. This is a real
  finite certificate check — but of primality/ladder geometry, **not** of Goldbach.
* The repo's own conclusion is visible in the docs: no pointwise binary
  Goldbach proof is claimed even under GRH/ERH.

**Claimed but unverified here:**

* Every Lean elaboration claim, including "lake build passes", theorem types,
  `#print axioms` results, and the zero-axiom comments. No build due to cache failure.
* The GRH circle-method Lemmas 1–5 in both proof markdowns (explicit formulae,
  zero-counting, singular-series product certificate, prime-power bounds).
* The finite binary verification through 4e18 (external literature; the local
  C++ run to 1e9 was not performed, and 1e9 ≪ 4e18).
* The local connection between the verified ladder certificates and the Lean
  axiom `certified_prime_ladder_1e22` (no Lean term was elaborated).
* All research-doc calculations: H1/H2/H3, GWX/Pascadi/LWW/Li–Liu statements,
  automorphic and Chebotarev hypotheses, parity/reflection countermodels. The
  four arXiv ids below are cited from local prose; the cited PDFs are **not in
  the cloned repo** (links point at `/tmp/…pdf` and `/home/nisbenz/…`), so they
  were neither fetched nor checked. No logical independence of Goldbach from
  GRH is proved — only failures of specific proof strategies.

**Speculation (explicitly labelled):** any suggestion that the GRH axioms could
be replaced by Helfgott's unconditional ternary theorem, or that one of the
blockers below is "probably solvable" with a named technique, is my strategic
guess, not a result of this audit.

---

## 5. Exact hypotheses of the conditional results

| Result | Hypotheses, stated exactly |
|---|---|
| Weak proof: all odd N ≥ 10²² = 3 primes | GRH for all nontrivial zeros of **every primitive Dirichlet L-function including ζ** (`weak_goldbach_proof.md:3-5`); BMOR Cor 1.2 zero count; Backlund zeta bound; Rosser–Schoenfeld ψ≤1.03883x and ψ−θ≤1.42620√x; explicit product certificate; finite binary verification through C=4e18; (for the full conjecture) a prime ladder with gaps ≤C−4. |
| Binary exceptional proof: E(X) ≤ 2e6√X log³X, X≥4 | GRH for all primitive Dirichlet characters **including conductor 1** (`binary_goldbach_exceptional_proof.md:3`); same primitive-character inequality (1) and product certificate; Rosser–Schoenfeld bounds; finite binary verification through X₀=4e18. |
| H1 reduction (`research.md:24`) | Dirichlet GRH + finite verification + **H1**: `F_N(T∖A) ≥ −0.764480 N` for every even N>C, A = two arcs at 0, 1/2 of half-width (17/4)/(2πN). Only zeta RH needed for the major arcs. |
| H2 reduction (`research.md:84`) | Same + **H2**: `F_N(T∖A_y) > −NJ(T_y)D_H(N)+Nd_y+b_N`, with H=⌊2(N/C)^{1/16}⌋; uniform `F_N(T∖A_y) ≥ −N/3` suffices. |
| H3 reduction (`research.md:197`) | **RH** + finite verification + **H3**: `U_N ≥ −(1−1.05·10⁻⁷)κN` with κ=N/φ(N), U_N the centered reduced-residue correlation. |
| Parity divisibility model (5) | RH consequence `Σ_{m≤t}λ(m) ≪_η t^{1/2+η}`; fixed 0<η<1/4; squarefree d coprime to N. Finite-modulus refinement needs fixed-character GRH. |
| Automorphic parity theorem (7) | Fixed tempered cuspidal GL_r/ℝ; automorphic RH for L(s,π); temperedness bound on A_π(p^j); fixed-degree Lindelöf; finite-place Ramanujan/archimedean gap as granted in `erh_attack.md:7`. |
| z=N^{2/9} reduction (8) | Dirichlet GRH; lower linear sieve at D=√N/log¹⁰N; **unproved** `H(N) ≤ (f_*−ε)N V_N(z)` with f_*=(8e^γ/9)log(5/4). |
| Chen one-sided reduction (9) | Quantitative Chen theorem (positive supply c𝔖(N)N/L²), squarefree Chen complements; **unproved** bias condition `limsup B_C(N)L²/(𝔖(N)N) < c`; no explicit c,N₀. |
| GWX theorem (ratios doc §1) | Hypothesis 1.1 of arXiv:2611.18825v1: conjugate characters, ω_D∈(0,1/2] fixed independent of small η, numerator Re=1/2, denominator Re=1/2+η, |t|≤100log(2q), error O_{η,ε}(q^{1−ω_D+ε}(1+T)^B); plus ω_D>2η at derivative disks. |
| Ratios estimates (1)–(3), O(q^{−η+ε}) | Dirichlet GRH for 1/L on Re=1/2+d; fixed small η; smooth mollifier length q^θ or joint product length Y=q; height window |t|≪log q; parity projectors; modulus q>1. |
| Signed moment (7a), B_q(η)≪q^{1−2η+ε} | Dirichlet GRH; joint cutoff Y=q²; fixed 0<η<1/4; cancellation **not** assumed in the retained sum, but the detector needs the *signed* value at each even N. |
| Moving-line criterion (7)/(8) | η_q=c/log(2q); `B_q(η_q)=o(φ*(q))` (or finite-endpoint inequality (8) for all N>C with N/2 composite); plus an explicit asymptotic-to-all-even bridge. |
| Pascadi 8/15 and 0.532 | Selberg eigenvalue conjecture (removes exceptional spectral terms); supplied arXiv:2611.34917v1 statements; height aspect for 0.532/8/15, not conductor aspect. |
| Li–Liu exponents | Unconditional arXiv:2606.05224v2 Thm 1.1 (margin 0.0004 in C(N) units); Thm 1.3 under **WEH(0.999)** (weighted Elliott–Halberstam, margin 0.062); repo narrowing to 1.8999998 / 1.39998 uses Selberg upper sieve and (13). |
| Exact subtraction identity (`persistent_push.md` (2)) | Dirichlet GRH; q>1; smooth compactly supported test W in positive quadrant. It is an identity, not an estimate. |

---

## 6. Blockers on the route to pointwise binary Goldbach

Extracted from the four research docs. "Attack angle" = concrete next step
suggested by the docs or (where marked *my suggestion*) by me. Papers marked
"supplied" are cited in the docs but their PDFs are not in the repo and were not
independently verified here.

### From `strong_goldbach_research.md`

1. **1/4 mean-square gap.** L² Fourier error ≲1600N^{5/2}L³ gives a *single*
   coefficient allowance ~40N^{5/4}L^{3/2}; positivity needs ~N — exponent gap
   exactly 1/4. No arXiv id (uses companion binary proof). Why blocks: Markov over
   dyadic blocks only controls count of exceptions, not the sign at a fixed target.
   Attack: prove a pointwise signed minor-arc estimate (H1/H2) rather than
   substituting exceptional-set averages; investigate higher-moment/quasi-RH
   exceptional counts (*my suggestion*: these still allow isolated exceptions).
2. **Zero-pair T^{3/2}log²T block.** Same-sign zeta zero pairs in kernel (4) have
   inverted magnitudes ≍T^{-1/2} with ≍T log T pairs per block ⇒ T^{3/2}log²T at
   T≈N; the Gamma phases and N^{i(γ+γ')} survive; absolute summation fails. No
   arXiv id. Why blocks: GRH fixes Re ρ=1/2 but not the sign/cancellation of (4).
   Attack: weighted conductor-uniform pair-correlation estimate after summing
   centers, valid at each even N; do **not** assume ordinary Montgomery pair
   correlation is applicable.
3. **Parity countermodel to every level <1.** Weights a_n^±=K⁻¹w(n)(1±λ(n))
   with h(p)=1/(p−2) satisfy divisor-test asymptotics to any fixed level below 1
   under RH, yet the plus sequence has no primes. Why blocks: any sieve-only
   deduction from those linear tests cannot distinguish primes. Attack: a
   bilinear test Σ a_{dk}λ(d)λ(k) with strict domination; or an independent
   two-form theorem for genuine Λ coefficients.
4. **Fourier reflection hole in Z/MZ.** A random half of each ±orbit has
   (1_D*1_D)(0)=0 while all nonzero Fourier coefficients are O(√(M log M)).
   Why blocks: small individual coefficients plus density do not force the
   reflection center; the signed square-sum cancels the missing zero frequency.
   Attack: use positivity/average over multiple centers or a kernel with
   controlled signed energy; note the ternary problem has an extra Fourier factor.
5. **Unproved signed inputs H1/H2/H3.** Each conditional theorem reduces
   all-even Goldbach to excluding a large negative correlation at one frequency
   per even N; none is established. Attack: target H2's growing major arcs with
   a zero-density or Deuring–Heilbronn input? (*my suggestion*: speculative.)
6. **Missing two-form / dispersion estimate.** Off-diagonal
   Λ(N−dk₁)Λ(N−dk₂) with k₂−k₁ fixed cannot be handled by shifted-divisor or
   divisor-decomposition transfers; pair correlation involves sums γ+γ′, not
   differences. Attack: Kuznetsov/delta-method applied to the actual Λ
   coefficients with retained lengths and signs.

### From `strong_goldbach_erh_attack.md`

7. **Lü–Wang–Wu support vanishes on the rough set.** Their auxiliary weight
   W(m) (eqs 2.12–2.13) requires a prime in each of K disjoint subpower intervals
   exp(L^{a_i}), 1/10<a_i<1/5, so `1_{P⁻(m)>N^θ}W(m)=0` for all fixed θ>0.
   arXiv:2610.20242v2 (supplied). Why blocks: an unrestricted o(π(x)) can lose
   the entire restricted average; at scale N/L² an error N/L suffices to hide it.
   Attack: design weights supported on rough/Chen complements, or prove a
   target-uniform reflected statement with an explicit denominator lower bound.
8. **Prime-square indicator error.** `(1−μ(m))/2` misweights squares; on
   P⁻(m)>N^{1/3} the exact prime indicator is `(1−λ(m))/2`, with up to √N squares
   to subtract. Why blocks: quantitative applications need S−Q positive and B
   strictly smaller. Attack: use the Liouville form and bound the square term.
9. **Lower sieve dies at z=N^{1/3}.** GRH progression level D≈N^{1/2} gives
   s=log D/log z≈3/2≤2, where the dimension-one lower function is zero; need
   level >N^{2/3}. arXiv: none. Attack: z=N^{2/9} with marked divisor (blocker 10),
   or Chen's proven supply (blocker 11).
10. **Marked-divisor bias H(N) unestimated.** At z=N^{2/9}, (8) needs
    H(N)≤(f_*−ε)NV_N(z); LWW weights vanish there too. Why blocks: no known
    GRH estimate for the signed rough parity sum. Attack: dispersion over
    p≡N mod r for z<r≤N^{1/3} with explicit constants.
11. **Chen-set Möbius bias B_C(N).** (9) has a positive supply c𝔖(N)N/L² but
    needs limsup B_C(N)L²/(𝔖(N)N)<c; c,N₀ not explicit; no finite bridge.
    Attack: prove cancellation/bias on Chen candidates; derive explicit constants.
12. **Automorphic/Frobenius tests don't see reflection.** Theorem (7) shows the
    prime-free model passes all fixed smoothed GL_r tests at every level <1;
    Chebotarev controls a single prime's Frob, not two primes summing to N.
    arXiv for LWW: 2610.20242v2. Attack: joint norm-form/two-prime counts or
    two-input tests; not a logical independence result.
13. **Balanced box d,k≈√N.** Individual GRH errors ∑√N log²N over √N progressions
    lose everything; "Grand RH for GL_n" supplies no single exponent for the
    Type I/II/III + sharp-cutoff collection. Attack: evaluate (4)'s off-diagonal
    via spectral methods with actual Λ coefficients.

### From `strong_goldbach_nov2026_ratios_attack.md`

14. **Reciprocal truncation budget θ>2.** GRH gives substitution error
    q^{−θη+ε} for M=q^θ; GWX need saving >2η ⇒ θ>2 (before interpolation);
    separate cutoffs give only η/(2(1−η)); moving line η=c/log q needs
    log M ≍(log q)². arXiv:2611.18825v1 (GWX, supplied). Attack: joint product
    cutoff gives q^{−η+ε} — still η short of the detector.
15. **Critical q^{1−2η} barrier and model size.** Direct signed moment reaches
    B_q(η)≪q^{1−2η+ε}, but H_p(σ,σ)/p^{1−2η} tends to a nonzero constant, so a
    triangle bound on A_p and H_p separately cannot give o(p^{1−2η}); the
    detector needs the signed cancellation. Attack: estimate E_q=A_q−H_q directly
    with the common height phase retained; or bypass differentiation via (7).
16. **Pascadi exponent mismatch.** 0.532 concerns a zeta **height** integral,
    8/15 needs Selberg; no fixed-q, two-reciprocal, both-parities, composite-q
    moment is stated. arXiv:2611.34917v1 (supplied). Attack: establish the
    conductor-local moment at gwX shifts; don't substitute height-aspect lengths.
17. **Parity/disk differentiation losses.** Recovering parity from undifferentiated
    ratios costs η^{-2} on disks and 1/η near x+y=0; a bare uniform o(q) cannot be
    differentiated twice and inverted. Attack: formulate the criterion directly
    on the differentiated signed moment (4)–(5), i.e. (7).
18. **Sparse conductor sets.** For N=2p only conductor p carries the family;
    for N=2^k the top conductor carries 1/2, top r carries 1−2^{-r}; no growing
    average can hide a worst-case error. Attack: exact cancellation across the
    sparse divisors, or the finite-endpoint inequality (8) at every target.
19. **Asymptotic ⇒ all-even gap.** Any o(N) result needs an explicit bridge to
    C=4e18 or condition (8) for N>C. Attack: make constants explicit.

### From `strong_goldbach_persistent_push.md`

20. **Exact subtraction residual.** Identity (2) leaves Σ b_q(h){G_{q,W}(h)−
    𝔖(h)F₊(h)} − Δ(diagonal) − Δ(fixed-difference); leading term is the weighted
    prime-pair count minus the singular-series integral on each line. No estimate.
    Attack: prove positivity of this residual for every even N under GRH; this is
    the cleanest reformulation of the missing input.
21. **Positive-definite kernel impossible.** A positive-semidefinite w(u+v) with
    w(1)=1 cannot have w(k)≤0 for k≥2; rank-one squared norms give a *difference*
    of parity energies, not an ordering. At N=8 an admissible smooth test gives
    exactly −N𝔖(N). Attack: signed minorant (9) retaining nearly all main term,
    plus control of the proper-prime-power contribution; the sign example shows
    automatic positivity fails.
22. **Surviving Pascadi/Selberg frequency term.** After Selberg, √(qA)/M remains
    constant in the outer frequencies; 8/15 is a height-aspect supremum from his
    §5.1, not a conductor endpoint. arXiv:2611.34917v1. Attack: Bettin–Chandee
    trilinear theorem controls a balanced sub-block with power saving; full moment
    still needs zero frequency + both parity projectors + long reciprocals.
23. **Li–Liu exponent cannot reach 1.** Continuity bound (13) gives
    a=1.8999998 / 1.39998 (WEH(0.999)), but the accumulated loss diverges as
    b↓1; arXiv:2606.05224v2. Attack: new supply estimates carrying parity
    information, not just quantitative counts.
24. **Prime-free sequence with more mass than the narrowed supply.** The
    synthetic a_m^+/log N has ≥(log(7/6)−o(1))𝔖(N)N/L² on semiprimes
    r∈(N^{1/4},N^{7/25}], exceeding (14)'s baselines (0.00011 / 0.016). Why blocks:
    supply + linear sieve tests alone still cannot exclude the composite model.
25. **Largest-conductor reflection hole.** On N=2^k or 2p² there is a nonnegative
    f on units with f(x)f(−x)=0, zero coefficients below the top primitive
    conductor, and all centered Fourier/character sums O(√(N log N)); the top
    family supplies exactly −φ(N). Why blocks: lower-conductor uniformity,
    near-square-root Fourier bounds and principal mass knowledge are jointly
    compatible with a full deficit at one conductor. Attack: bound the top
    conductor's signed moment directly (identity (11)/(16)); do not average it away.

**Cross-cutting blocker (my label):** no single one of these is a theorem that
GRH *cannot* imply Goldbach. The docs construct failures of specified
deductions. Claiming logical independence would be speculation.

---

## 7. Toolchain / environment notes

* `~/.elan/toolchains` after audit: v4.16.0 (added), v4.33.1, v4.34.0, v4.34.1
  (default), v4.36.0. In the scratch dir, `elan show` selected 4.16.0 via
  `lean-toolchain`, and `lake --version` reported Lake 5.0.0-128a1e6 / Lean 4.16.0.
* `lake exe cache get` produced no output and timed out twice (300 s, then 90 s);
  `.lake/packages/` stayed empty. `curl` to github.com returned HTTP 200, but
  the Mathlib cache host name `matlib.cmu.edu` did not resolve from this
  environment. Building Mathlib from source would exceed the 15-minute budget,
  so `lake build` was intentionally not attempted.
* Consequently **no theorem in this repo is recorded as `checked`** in the
  framework's sense (AGENTS.md §0). Recommended mapping: put the Python numeric
  checks and ladder certificate check in `checked` with their narrow statements;
  put the Lean theorems in `unverified/conditional (axiom-dependent)`; keep all
  H1–H3 / GWX / Pascadi / Chen / WEH items `conditional` with the exact
  hypothesis in the claim id; keep pointwise binary Goldbach `open` under GRH/ERH.
* Writes were restricted to `audit/REPO_AUDIT.md`, `audit/claim_inventory.json`,
  `audit/PROGRESS.md` (at parent's explicit request) and scratch files under
  `/tmp/opencode/goldbach_audit/`. The cloned repo itself was left untouched.
