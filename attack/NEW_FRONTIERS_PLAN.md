# New-Frontiers Attack Plan (Wave 6) — Beyond $\mathrm{GL}_1$ Circle Method & Sieves

**Date:** 2026-11-27  
**Baseline:** Waves 0–5 completed (`22` checked claims, `6` resolved blockers, `11` open blockers; all 4 classical/Nov-2026 $\mathrm{GL}_1$ routes now have proved structural barriers).

---

## 0. Strategic Shift

Waves 0–5 systematically tested and barrier-proved every standard $\mathrm{GL}_1$ attack family:
1. ERH Farey/ultra-low-zero circle method (`B-002`/`B-010`/`B-011`) — fixed-$q$ unitary wall & cross-$q$ linear resonance wall.
2. Distribution-level sieves, Selberg majorants, and LWW/Lichtman small-prime Möbius cancellation (`B-003`/`B-005`/`B-012`/`B-015`) — exact ceiling $0$ at $\theta=1$, Selberg infimum $= 2$, and zero support on semiprimes.
3. GWX / Lee fixed-shift $2/2$ Dirichlet ratios + Pascadi height-aspect moments (`B-004`/`B-014`) — ERH sits at $1 - 2\eta + \varepsilon$ with zero strict saving.

Wave 6 opens **two genuinely outside-the-box mathematical frontiers** untouched in Waves 0–5:

| Strike | Blocker / Issue | Frontier Mechanism | Concrete Pass Threshold |
|---|---|---|---|
| **2A** | `B-005` (#5) | **Unconditional Function-Field Goldbach Transfer** — dissect GWX (`arXiv:2611.18825v1`, `m4.tex:2778–3265` & `3475–3577`) Sawin–Shusterman cutoff at $5/6$ + discriminant cohomology + reciprocal-ratios/Chowla bridge, and translate to $\mathbb{Z}$ | Identify the exact $\mathbb{Z}$-transfer identity at cutoff $D = N^\alpha$ (short Type I vs long tail $\sum_{k < N^{1-\alpha}}\sum_{p\equiv N\pmod k}\Lambda(p)\mu((N-p)/k)$ where $(N-p)/k$ is **typical**, escaping Lichtman's semiprime zero-support wall!) and test whether prime EH / ERH + Lichtman / Chowla closes the log-power budget — or prove the exact quantitative gap |
| **2B** | `B-012` (#9) | **$\mathrm{GL}_2$ / $\mathrm{SL}_2(\mathbb{Z})$ Automorphic Spectral Theory** on the Wave 5 Strike 1A four-prime determinant $q_2 p_1 - q_1 p_2 = N(q_2 - q_1)$ | Beat the **normalized off-diagonal threshold $< 4$** in the direct Cauchy–Schwarz expansion of the central semiprime band $S_\delta(N)$ (where diagonal is already $o(1)$) using Vaughan/Heath-Brown + Voronoi + Kuznetsov / spectral large sieve (testing unconditional, Selberg $\theta_2=0$, and $\mathrm{GL}_2$ Grand RH) $\implies$ **$c < 2 \implies$ Strong Goldbach under prime EH**, or prove the exact $\mathrm{GL}_2$ spectral barrier |

---

## Phase 1 — Parallel New-Frontiers Execution (2 `gpt-6.2-astra` `high` Agents)

### Strike 2A — Function-Field Unconditional Goldbach Transfer (`B-005`, `#5`)
1. **Source audit of `m4.tex:2778–3265` (`Binary prime problems over function fields`) and `3475–3577` (`Reciprocal ratios and Chowla`):**
   - Extract the exact Sawin–Shusterman–GWX decomposition splitting one von Mangoldt factor at cutoff $5n/6$ (short divisors via squarefree progressions vs long divisors via discriminant/resultant cohomology) and the reciprocal-ratios/Chowla equivalence.
2. **Exact $\mathbb{Z}$-analogue & escaping the semiprime zero-support wall:**
   - Formulate the exact $\mathbb{Z}$-identity splitting $\Lambda(N-p) = -\sum_{d\mid N-p}\mu(d)\log d$ (or smooth Vaughan/Möbius cutoff) at $d \le N^\alpha$ vs $d > N^\alpha$ ($k = (N-p)/d < N^{1-\alpha}$).
   - Notice: unlike Chen/semiprime sets, for small $k < N^{1-\alpha}$ the complement $(N-p)/k$ runs over **typical** integers (not rough/semiprime!), so Lichtman's (`2611.28392v1`) exact prime-interval partition has **full support** here!
   - Compute the **exact log-power & uniformity budget** required on $\sum_{k < N^{1-\alpha}} \sum_{p \equiv N \pmod k} \Lambda(p)\mu((N-p)/k)$ as $\alpha \uparrow 1$ (under prime EH, BV, or ERH), and check whether smooth cutoff / bilinear averaging over $k$ / reciprocal-ratios Chowla (`m4.tex:3475–3577`) can close the gap — or prove the exact deficit (both in log-power and in $k$-uniformity / reflection determinant $N(b-a)$).
3. **Discriminant / squarefree-factorization hypothesis over $\mathbb{Z}$:**
   - State the minimal clean $\mathbb{Z}$-analogue of GWX's function-field discriminant cancellation (comparing its logical strength to ERH, EH, Chowla, and GWX's Ratios Conjecture).

### Strike 2B — $\mathrm{GL}_2$ Automorphic Spectral Theory on the Four-Prime Determinant (`B-012`, `#9`)
1. **Exact Cauchy–Schwarz off-diagonal formulation from Strike 1A (`attack/audit/B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md`):**
   - Pin down the exact four-prime off-diagonal sum $O_\delta(N)$ whose normalized size $< 4$ proves $c < 2$ (and hence Strong Goldbach under prime EH), verifying the exact singular-series normalization and $o(1)$ diagonal.
2. **$\mathrm{GL}_2$ shifted-convolution / Kuznetsov / Voronoi spectral analysis:**
   - Apply Vaughan/Heath-Brown decomposition (or upper-bound majorant on one prime variable + genuine $\Lambda$ on the other) to the bilinear determinant $q_2 p_1 - q_1 p_2 = N(q_2 - q_1)$ ($q_1, q_2 \in (N^{1/2-\delta}, N^{1/2}]$).
   - Track the exact conductor, shift $h = N(q_2 - q_1)$, archimedean weight, and spectral parameters through Voronoi summation + Kuznetsov trace formula + Deshouillers–Iwaniec / Blomer–Harcos / Assing–Blomer–Li spectral bounds.
   - Evaluate the exact exponent ledger under three regimes: (i) unconditional ($\theta_2 = 7/64$), (ii) Ramanujan–Petersson / Selberg ($\theta_2 = 0$), and (iii) **$\mathrm{GL}_2$ Grand RH** (for cuspidal automorphic $L$-functions and Rankin–Selberg convolutions).
3. **Exact binary outcome:**
   - Either prove normalized off-diagonal $< 4$ under one of the three regimes (breakthrough!) OR prove the exact spectral-parameter / diagonal-re-entry obstruction showing why $\mathrm{GL}_2$ spectral theory still leaves normalized off-diagonal $\ge 4$ (or fails to cancel the off-diagonal main term).

---

## Phase 2 — Decision Gate
- **If 2A or 2B opens a genuine breakthrough (unconditional, ERH, EH, or $\mathrm{GL}_2$ Grand RH):** Red-team audit $\to$ explicit constants $\to$ Lean 4 formalization.
- **If both 2A and 2B prove sharp structural barriers:** Record both new barrier theorems cleanly, then execute **Branch C** (upstream all checked Lean ground + discharge `certified_prime_ladder_1e22` + write `attack/FINAL_REPORT.md` and push cleanly).

---

## Usage & Rigor Guardrails
- **Budget:** 2 `gpt-6.2-astra` (`high`) agents in parallel — strictly usage-aware (cached `.tex` files + existing `/tmp/astra_w2_b011/venv/bin/python`, `< 10s` scripts, no web downloads) with zero compromise on mathematical rigor.
- **Honesty:** Every claim tagged `[Q]`/`[P]`/`[I]`/`[U]`; exact line citations; no false premises; no map/git edits by children.
