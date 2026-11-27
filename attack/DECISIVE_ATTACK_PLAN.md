# Decisive Attack Plan — Strong Goldbach Conjecture

**Date:** 2026-11-27  
**Baseline commit:** `60775cf` (`origin/main`)  
**Honest baseline:** Strong (binary) Goldbach is **OPEN** (including under ERH) both in this repository (`22` checked claims, `6` resolved blockers, `11` open blockers across Waves 0–4) and on arXiv `math.NT` through 27 Nov 2026.

---

## 0. Why This Plan Is Different (Four Live Doors, Zero Decoys)

Waves 0–4 eliminated every decoy and secondary technicality: high zeros ($|\gamma| \ge 2\log\log N$), pole–zero cross terms, $\beta$-integration, global $L^r$ Hölder bounds, distribution-level-only switched sieves up to $\theta = 1$, Lü–Wang–Wu's averaged prime-weight route (zero support on rough/Chen sets), and per-$q$ unsigned/unitary norm bounds.

Meanwhile, our live arXiv audit through **27 Nov 2026** surfaced **two brand-new November 2026 techniques not yet audited in Waves 0–4**, giving us **exactly three surgical, non-overlapping breakthrough doors**:

| Strike | Blockers / Issues | Core Target | Brand-New Weapon (Nov 2026 + Wave 4) | Decisive Pass Threshold |
|---|---|---|---|---|
| **1A** | `B-005`, `B-012`, `B-015` (#5, #9, #12) | Parity breaking on central semiprime / Type II band | **Lichtman (`arXiv:2611.28392v1`, 20 Nov 2026)** exact prime-interval partition + graph expansion **AND** Cauchy–Schwarz dispersion + **Pascadi (`arXiv:2611.34917v1`, 25 Nov 2026)** Kloosterman fractions on $q \in [N^{1/2-\delta}, N^{1/2}]$ | **Either** upper-bound constant **$c < 2$** on a single central semiprime band $p + qr = N$ ($\implies$ Strong Goldbach under prime EH), **or** genuine signed Type II on $[N^{0.4383}, \sqrt{N}]$ ($\implies$ Strong Goldbach unconditionally from BV Type I) |
| **1B** | `B-004`, `B-014` (#4, #11) | Weak-exponent, fixed-shift $2/2$ Ratios bridge | **SeungJu Lee (`arXiv:2610.32672v2`, 23 Oct 2026)** fixed-shift ($\operatorname{Re} \in [3/64, 5/64]$), crossed-zero-residue opposing-weight method (needs only error exponent $\vartheta < 7/8$ under RH!) + **GWX (`arXiv:2611.18825v1`, 13 Nov 2026)** + **Pascadi (`2611.34917v1`)** | Transfer Lee's weak-exponent ($\vartheta < 7/8$ under RH/ERH) mechanism to Binary Goldbach $N = p_1 + p_2$ and test whether ERH + Pascadi Kloosterman bounds cross $\vartheta_{\rm needed}$ (or establish the exact minimal gap $\vartheta_{\rm proved} - \vartheta_{\rm needed}$) |
| **1C** | `B-011`, `B-002` (#8, #2) | Signed ultra-low-zero cancellation under ERH | Wave 4 $Q = \lfloor N^{2/3}\rfloor$ reduction ($|\gamma| < 2\log\log N$, distinct large-product-conductor pairs): sum over **$q$ first** via reverse explicit formula + **Bettin–Chandee / Pascadi** bilinear Kloosterman sums, guided by real-zero anatomy of $\mathcal{P}_N^\circ(q)$ | Prove $\liminf_{2\mid N\to\infty} \mathcal{P}_N^\circ > -1/3$ under ERH ($\implies$ Strong Goldbach under ERH), **or** construct an admissible low-zero spectral countermodel proving $\mathcal{P}_N^\circ \le -\mathfrak{S}(N)/e$ survives ERH + low moments |

Every strike obeys `AGENTS.md` §0 & §8: **no false premises, no hidden axioms, every claim tagged `[Q]`/`[P]`/`[I]`/`[U]`**, and every numerical check capped at `< 10s` runtime.

---

## Phase 1 — The Decisive Three-Strike Wave (3 `gpt-6.2-astra` `xhigh` Agents)

### Strike 1A — Lichtman Exact Partition + Central Semiprime Dispersion (`B-005` / `B-012` / `B-015`)
1. **Audit Lichtman (`arXiv:2611.28392v1`, 20 Nov 2026) directly from source:**
   - Download/inspect the actual paper (`arxiv.org/pdf/2611.28392v1` or HTML) — do not rely on the abstract.
   - Check whether replacing Lü–Wang–Wu's averaged prime weights with Lichtman's **exact partition of prime intervals** + Poisson–Dirichlet determinant + graph expansion **escapes the zero-support obstruction** on rough/Chen complements ($N - p = q_1 q_2$ with $q_1 \approx q_2 \approx \sqrt{N}$).
   - Determine the exact exponent barrier: why does Lichtman get $(\log x)^{-1/2+\varepsilon}$ on $\sum_{p\le x} \mu(p+2)$ instead of $(\log x)^{-1-\delta}$, and can reflection $N-p$ + ERH/EH push past $(\log N)^{-1}$ or give a non-trivial saving on a localized semiprime band?
2. **Direct dispersion attack on a single narrow central semiprime band $q \in [N^{1/2-\delta}, N^{1/2}]$:**
   - Wave 4 proved that under ordinary prime EH ($\theta \to 1^-$), **any** fixed upper bound $< (2 - \varepsilon)\,\text{HL}$ on a *single* narrow band $p + qr = N$ ($q \sim N^{1/2-\delta/2}$) settles Strong Goldbach — no full asymptotic needed!
   - Apply Cauchy–Schwarz in $q$ (or $r$) + Kloosterman/Estermann dispersion + **Pascadi (`2611.34917v1`)** bilinear Kloosterman-fraction savings to $\sum_{q \in I} \sum_{p + qr = N} \Lambda(p)\Lambda(q)\Lambda(r)$ (or a nonnegative upper-bound majorant on $r$).
   - **Exact binary outcome:** Either beat constant $2$ (breakthrough under prime EH!) or compute the closed-form diagonal/off-diagonal balance proving whether Cauchy–Schwarz on $q \sim \sqrt{N}$ forces diagonal $\ge 2 \times \text{main term}$.
3. **Optional quick refinement:** Tighten the Wave 4 unconditional BV Type II interval $[0.43835, 0.47560]$ via 4-level/5-level Ford–Maynard minorant in 200-bit Arb (`< 5s`) if time permits.

### Strike 1B — Lee Fixed-Shift Weak-Exponent Ratios Bridge (`B-004` / `B-014`)
1. **Audit Lee (`arXiv:2610.32672v2`, 23 Oct 2026) + GWX (`arXiv:2611.18825v1`, 13 Nov 2026) + Pascadi (`arXiv:2611.34917v1`, 25 Nov 2026) from actual arXiv sources:**
   - Verify Lee's exact mechanism: real shifts fixed in $[3/64, 5/64]$ (NOT $\eta \to 0$!), crossed zero residues retained in Mellin inversion, two opposing nonnegative time weights isolating the difference $h$, yielding Hardy–Littlewood prime-pair asymptotics from a $2/2$ zeta-ratios error $O(U^{\vartheta+\varepsilon})$ with $\vartheta < (39-\sqrt{177})/32 \approx 0.803$ unconditionally and **$\vartheta < 7/8 = 0.875$ under RH**.
2. **Port Lee's mechanism to Binary Goldbach ($N = p_1 + p_2$):**
   - Check whether Lee's fixed-shift opposing-weight cancellation works in the **Dirichlet character / conductor aspect** (as in GWX) or directly via a **shifted/reflected $2/2$ ratio for $L(s,\chi)$**, and compute the exact admissible error exponent $\vartheta_{\rm GB}^{\rm RH}$ (does fixed shift eliminate the $\omega_D > 2\eta$ cliff that blocked `B-004` in Waves 1–3?).
3. **Compare $\vartheta_{\rm GB}^{\rm RH}$ against what ERH + Pascadi (`2611.34917v1`) actually prove:**
   - Compute the best provable $2/2$ ratio error exponent $\vartheta_{\rm proved}$ under ERH + Pascadi's Nov 25 bilinear/trilinear Kloosterman-fraction bounds ($N^{1/12} A^{1/3}$ saving, twisted second moment to $T^{0.532}$).
   - **Exact binary outcome:** Either $\vartheta_{\rm proved} < \vartheta_{\rm GB}^{\rm RH}$ (breakthrough proof of Strong Goldbach under ERH!) or an exact, verified exponent ledger showing the remaining gap $\vartheta_{\rm proved} - \vartheta_{\rm GB}^{\rm RH}$ and the exact sharpest conditional theorem provable from Lee + GWX + Pascadi.

### Strike 1C — Cross-$q$ Cancellation & Real-Zero Anatomy of $\mathcal{P}_N^\circ$ (`B-011` / `B-002`)
1. **Fast numerical anatomy of $\mathcal{P}_N^\circ(q)$ (`< 10s` Python/Arb script):**
   - Using actual low Dirichlet zeros ($|\gamma| < 2\log\log N$, verified via `mpmath`/Arb) for small/moderate even $N$, compute the per-$q$ contributions $\mathcal{P}_N^\circ(q)$ across $q \in (Q/L^4, Q]$.
   - Measure the crucial structural question: is the cancellation $\mathcal{P}_N^\circ \approx 0$ happening **inside each fixed $q$** (alignment of the low-zero vector $b_{\chi^*}$ against the trimmed matrix $M_q^\circ$) or **only when summing across moduli $q$**?
2. **Sum over $q$ first (Reverse Explicit Formula + Bilinear Kloosterman):**
   - Wave 4 proved every fixed-$q$ matrix norm fails because $G_q(\chi\chi'; -N)/\varphi(q)$ is unitary. Bypass fixed-$q$ bounds completely: rewrite $b_{\chi^*}$ via its smooth prime/Mellin representation (cutoff height $2\log\log N$), bring the $q$-sum $(N^{2/3}/L^4, N^{2/3}]$ **inside**, and apply **Deshouillers–Iwaniec / Bettin–Chandee / Pascadi (`2611.34917v1`)** bilinear Kloosterman-fraction bounds to the $q$-sum of $\sum_a^* \ell_{q,a}(\chi\chi')(a)e(-Na/q)$.
3. **Spectral obstruction test (red-team backup):**
   - If the cross-$q$ exponent ledger still hits a wall, construct an explicit ERH-admissible synthetic low-zero spectrum matching GUE/low-moment constraints that drives $\mathcal{P}_N^\circ \le -\mathfrak{S}(N)/e$ — proving precisely what multi-conductor zero-correlation beyond ERH is required.

---

## Phase 2 — Hard Go / No-Go Decision Gate

After Phase 1 completes and the parent re-verifies every calculation and source citation:

### Branch A — Breakthrough Path (Triggered if *any* of 1A, 1B, or 1C beats its Pass Threshold)
1. **Adversarial Red-Team Audit (1 `xhigh` Astra agent):** Dedicated solely to trying to *break* the candidate proof — check every contour shift, uniformity in $N$, character conductor, exceptional modulus, implicit constant, and edge case.
2. **Effective Onset & Finite Bridge (1 `high` Astra agent):** Make all constants explicit to compare the effective threshold $N_0$ against $4\times 10^{18}$, and design the finite bridge if $N_0 > 4\times 10^{18}$.
3. **Lean 4 Formalization Sprint:** Formalize the core new theorem and supporting lemmas in Lean 4 with full kernel replay (`Environment.replay`), `#print axioms` audit (`propext`, `Classical.choice`, `Quot.sound` only), and zero banned tokens.

### Branch B — Sharp Conditional Breakthrough (Triggered if a Strike proves a strictly new conditional Strong Goldbach reduction — e.g., weaker than GWX Ratios Conjecture, or a tighter unconditional $(1+a)$ bound below $1.9$)
1. Independently verify every constant and hypothesis.
2. Formalize the exact reduction theorem in Lean 4 (keeping the hypothesis explicit in the statement and ID per `AGENTS.md` §0).
3. Record the exact remaining gap cleanly on the matching GitHub issues.

### Branch C — Definitive Structural Closure & Checked-Ground Hardening (Triggered if all 3 Strikes prove sharp, irreducible barriers)
Stop burning research tokens on blocked analytic routes and execute **2 focused `medium` engineering/formalization agents** to lock in permanent checked ground:
1. **Track 2A — Upstream Checked Lean Ground & Native Strict Replay Checker:**
   - Upstream all verified `v4.16.0` Lean micro-lemmas (`GB-B002-CENTERING`, `GB-B004-DYADIC`, `GB-B010-MOMENT`, `GB-B012-WEIGHTED`, `GB-B013-U16`, `GB-B015-MARKED`, plus any new Phase 1 Lean lemmas) and the 51-page `BinaryGoldbachUpTo 50000` generator + verifier into the repo, with a Goldbach-native `Environment.replay` checker alongside the unmodified vendored `pequalnp` checker.
2. **Track 2B — Eliminate `certified_prime_ladder_1e22` Axiom in `lean/WeakGoldbach/`:**
   - Replace `certified_prime_ladder_1e22` in `WeakGoldbach/Main.lean` with a batched kernel-checked Pratt certificate module (dropping `weak_goldbach_theorem` from **7 axioms to 6** — or, if full 2,501-rung replay exceeds the turn budget, land the deterministic generator + verified 100-rung milestone + one-command builder).

---

## Phase 3 — Parent Re-Verification, Final Report & Push

1. Parent independently re-verifies every Lean module, `#print axioms`, Arb/Python script, and arXiv source quote.
2. Update `attack/map/claims.json`, `attack/map/blockers.json`, `attack/map/feed.jsonl`, GitHub issues `#2`–`#12`, and regenerate `attack/site/dist/index.html`.
3. Write `attack/FINAL_REPORT.md` giving an unambiguous verdict (proved / conditionally proved under exact hypothesis / open with exact minimal barriers across all 4 modern routes).
4. Push cleanly to `main` (no co-author trailers) upon user confirmation.

---

## Resource & Discipline Guardrails
- **Phase 1 budget:** 3 `gpt-6.2-astra` (`xhigh`) agents running in parallel (one per independent door; zero redundant overlap).
- **Phase 2 budget:** 2 agents (`xhigh` for Branch A red-team/bridge, or `medium` for Branch C formalization).
- **Strict honesty:** Never tell any agent a solution already exists; every agent checks real arXiv sources (`2611.28392v1`, `2610.32672v2`, `2611.18825v1`, `2611.34917v1`) directly, runs fast `< 10s` scripts, and releases leases with exact honest reasons if blocked.
