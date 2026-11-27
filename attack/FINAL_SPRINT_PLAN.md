# Final Sprint Plan — Strong Goldbach Decisive Push

**Date:** 2026-11-27  
**Baseline commit:** `60775cf` (`origin/main`)  
**Current honest state:** Strong Goldbach is **OPEN** (including under ERH). `22` checked claims, `6` resolved blockers, `11` open blockers (all deeply audited across 13 Astra runs in Waves 0–4).

---

## 0. Strategic Premise (Honest & Usage-Aware)

Waves 0–4 eliminated every decoy and secondary technicality — high zeros ($|\gamma| \ge 2\log\log N$), pole–zero cross terms, $\beta$-integration, global $L^r$ Hölder bounds, distribution-level-only switched sieves up to $\theta = 1$, and unsigned/unitary norm bounds — leaving **exactly two razor-sharp mathematical targets** where a breakthrough could settle Strong Goldbach:

1. **Analytic Target (under ERH):** $\liminf_{2\mid N\to\infty} \mathcal{P}_N^\circ > -1/3$ at Farey order $Q = \lfloor N^{2/3} \rfloor$, involving **only** ultra-low zeros $|\gamma| < 2\log\log N$ and distinct large-product-conductor character pairs ($\operatorname{cond}(\chi\chi') > Q^{1/2-\delta}$).
2. **Arithmetic Target (BV / EH):** Either a genuine signed Type II comparison for $\Lambda(N - dk)$ on the **6.17%-wide central band $N^{0.4383} \le d \le \sqrt{N}$** (unconditional Type I), **or** under ordinary prime EH ($\theta \to 1^-$), **any** fixed upper-bound saving $c < 2$ on a single narrow central semiprime band $p + qr = N$ ($q \in [N^{1/2-\delta}, N^{1/2}]$).

Because settling a 284-year-old conjecture cannot be guaranteed in advance, this Final Sprint is structured in **3 gated stages** with strict usage caps:
- **Stage 1 (Breakthrough Strike — 2 `xhigh` Astra agents):** Go straight at Targets 1 and 2 using the strongest untried spectral/bilinear weapons.
- **Stage 2 (Go / No-Go Gate):**
  - **IF Stage 1 achieves a genuine analytic breakthrough** (a verified new saving beating the wall on Target 1 or Target 2): pivot 100% of Stage 2 into tightening constants, checking every edge case, bridging to $4\times 10^{18}$, and formalizing in Lean.
  - **IF Stage 1 proves both untried weapons hit a sharp structural barrier:** stop spending research tokens on dead ends and pivot Stage 2 into **irreversible checked-ground milestones** (eliminating `certified_prime_ladder_1e22` in Lean, upstreaming all verified Lean theorems + `BinaryGoldbachUpTo 50000` + native replay checker into the repo, and writing the definitive closure synthesis).

---

## Stage 1 — The Breakthrough Strike (2 Surgical `gpt-6.2-astra` `xhigh` Agents)

### Track 1A — Attacking $\mathcal{P}_N^\circ$ at $|\gamma| < 2\log\log N$ (`B-011` / `B-002`)
- **Goal:** Obtain genuine **signed cancellation** inside $\mathcal{P}_N^\circ$ (eq. 12–14 of `B011_B002_W4_DECISIVE_LOWZERO_PUSH.md`), where Wave 4 proved unsigned $L^2$ / unitary matrix norms cannot work.
- **Three concrete untried maneuvers (try in order, pivot fast if blocked):**
  1. **Direct numerical anatomy of $\mathcal{P}_N^\circ$** (fast `< 10s` script at small/medium $N$ with actual low Dirichlet zeros): measure how $\mathcal{P}_N^\circ(q)$ cancels **within** each modulus $q$ vs **across** moduli $q \in (Q/L^4, Q]$. Does sign cancellation happen inside a single $q$ (via $b_{\chi^*}$ orthogonality to the Kloosterman-weighted matrix) or only when averaging over $q$?
  2. **Reverse explicit formula + bilinear Kloosterman / Kuznetsov across $q$:** Replace $b_{\chi^*} = \sum_{|\gamma|<2\log\log N} \Gamma(1/2+i\gamma) N^{i\gamma}$ by its smooth Mellin/prime representation (length $\sim N$, smoothed to height $2\log\log N$) and sum over $q \in (N^{2/3}/L^4, N^{2/3}]$ **first**, applying **Deshouillers–Iwaniec / Bettin–Chandee / Pascadi bilinear Kloosterman bounds** to the $q$-sum of $\sum_a^* \ell_{q,a} (\chi\chi')(a) e(-Na/q)$. Check exact exponent ledger: does summing over $q$ save a power over the unitary per-$q$ bound?
  3. **Spectrum of the *trimmed* matrix $M_q^\circ$ & 4th-moment / cubic-moment cancellation:** Wave 4 proved the *full* matrix $G_q(\chi\chi'; -N)/\varphi(q)$ is unitary; check whether deleting diagonal/conjugate/small-conductor entries ($\operatorname{cond}(\chi\chi') \le Q^{1/2-\delta}$) or testing against **Conrey–Iwaniec / Young / Petrow–Young cubic & fourth moments** of $L(1/2+i\gamma, \chi)$ yields a signed bound $\mathcal{P}_N^\circ > -1/3$, OR prove an exact structural obstruction (e.g., constructing an admissible low-zero spectrum matching all low moments yet giving $\mathcal{P}_N^\circ = -\mathfrak{S}(N)/e$).
- **Success criterion:** Either a rigorous proof of $\liminf \mathcal{P}_N^\circ > -1/3$ (under ERH or ERH + explicit named moment conjecture) **or** a sharp obstruction proving what exact multi-conductor correlation is still missing.

### Track 1B — Attacking the Narrow Central Semiprime / Type II Band (`B-012` / `B-005` / `B-015`)
- **Goal:** Either narrow the unconditional BV Type II requirement even closer to $\sqrt{N}$ AND crack **one narrow central band** $q \in [N^{1/2-\delta}, N^{1/2}]$ for genuine $\Lambda(N - qr)$ ($c < 2$ under prime EH, or signed Type II under BV).
- **Three concrete untried maneuvers (try in order, pivot fast if blocked):**
  1. **Tighten the BV Type II threshold $[0.43835, 0.47560]$:** Optimize a 4-level/5-level Ford–Maynard minorant (and test a 5-prime obstruction) in 200-bit Arb to shrink the required unconditional BV Type II band width from 6.17% toward its true limit (~2.5–4%).
  2. **Dispersion / shifted-convolution attack on a single $\delta$-narrow central semiprime band $p + qr = N$ ($q \in [N^{1/2-\delta}, N^{1/2}]$):** Under prime EH ($\theta \to 1^-$), Wave 4 proved **ANY** upper-bound saving $c < 2$ on a *single* narrow band proves Strong Goldbach (no full asymptotic needed!). Test whether **Cauchy–Schwarz in $q$ + Kloosterman/Estermann dispersion + Weil/Kuznetsov** (exploiting that $q, r$ are BOTH localized within $N^\delta$ of $\sqrt{N}$, and only an upper bound $c < 2$ — not a two-sided asymptotic — is needed!) can beat the trivial factor $2$, OR derive the exact diagonal vs off-diagonal deficit showing why $c = 2$ resists dispersion.
  3. **Cross-check with the 4 external 2026 arXiv manuscripts (`B-014`/`B-015`):** If reachable (arXiv HTML/abstracts only, fast), verify whether GWX (`2611.18825`), Pascadi (`2611.34917`), Li–Liu (`2606.05224`), or Lü–Wang–Wu (`2610.20242`) contain any stronger range/hypothesis not captured in `proof/` that helps Track 1B.
- **Success criterion:** Either a genuine proof of $c < 2$ on a central semiprime band (yielding Strong Goldbach under prime EH!) or an exact Type II saving on $[N^{a_{\rm suff}}, \sqrt{N}]$, **or** a decisive barrier proof pinning down the exact off-diagonal deficit.

---

## Stage 2 — Decision Gate & Execution Branch

### Branch A (If Track 1A or Track 1B Breaks Through)
1. **Independent adversarial audit:** Dispatch a red-team `xhigh` Astra agent specifically to try to *break* the new proof (check every constant, contour shift, error term, edge case, and uniformity in $N$).
2. **Effective onset & bridge:** Make all constants explicit to compare $N_0$ against $4\times 10^{18}$ (and check if the `verify/` prime-ladder/sieve infrastructure can bridge any finite gap).
3. **Formalization sprint:** Formalize the new core theorem and its supporting lemmas in Lean with `#print axioms` and independent replay.

### Branch B (If Both Tracks Hit Irreducible Walls — Irreversible Checked-Ground Sprint)
Execute **2 usage-efficient (`medium` reasoning) engineering/formalization agents** in parallel:
1. **Track 2A — Upstream Checked Lean Ground & Native Strict Replay Checker:**
   - Port all **8 verified `v4.16.0` Lean micro-lemmas** (`B002` centering/reflection, `B004` dyadic projector, `B010` $L^p$ moment budget, `B012` weighted cube-root-rough detector, `B013` $U_{16}$ reflection hole, `B015` subcritical marked divisor) AND the **51-page `BinaryGoldbachUpTo 50000` generator + verifier** permanently into the repository (with a Goldbach-native `Environment.replay` checker that enforces exact type + `[propext, Classical.choice, Quot.sound]` + zero banned tokens, alongside the unmodified vendored `pequalnp` checker).
2. **Track 2B — Discharge `certified_prime_ladder_1e22` Axiom in `lean/WeakGoldbach/` (Optional Compute Budget: ~12–20 min build/replay, or prototype clean batched elimination):**
   - Replace the `certified_prime_ladder_1e22` axiom in `WeakGoldbach/Main.lean` with a batched kernel-checked Pratt ladder module using `WeakGoldbach.prime_of_lucas_trace`, dropping `weak_goldbach_theorem` from **7 axioms to 6** (leaving only the 5 analytic GRH axioms + `binaryGoldbach_4e18`) — OR, if full 2,501-rung build exceeds our session budget, land the complete deterministic generator + verified 50-rung / 100-rung milestone + one-command builder.

---

## Stage 3 — Final Verification, Closure Report & Push
1. Parent independently re-verifies every theorem, Lean build, `#print axioms` output, and numerical script.
2. Write the **Final Experiment Report** (`attack/FINAL_REPORT.md`) summarizing:
   - The exact status of Strong Goldbach (proved / conditionally proved / open with exact minimal barriers),
   - Every checked claim (`22+` → `30+`), every resolved blocker, and every open GitHub issue (`#2`–`#12`) with clean handoff notes,
   - Regenerated dashboard (`attack/site/dist/index.html`) and clean push to `main` (no co-authors) upon user confirmation.

---

## Usage Budget Summary
- **Stage 1:** 2 `gpt-6.2-astra` (`xhigh`) agents (maximum mathematical firepower on the only 2 live breakthrough shots, strict `< 10s` script cap, zero redundant re-reads).
- **Stage 2:** 2 `gpt-6.2-astra` (`medium` for Branch B engineering, or `xhigh` for Branch A red-team verification).
- **Total Sprint:** 4 Astra agents max — controlled, decisive, and guaranteed to leave either a real breakthrough or an airtight, permanently checked Lean + mathematical milestone.
