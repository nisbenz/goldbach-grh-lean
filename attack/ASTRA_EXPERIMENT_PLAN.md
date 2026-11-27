# Astra Orchestration Plan — Strong Goldbach Attack Experiment

**Date:** 2026-11-27  
**Coordinator:** Parent orchestrator (Gemini 4 Neon)  
**Workers:** Codex `gpt-6.2-astra` (`reasoningEffort: "high"`, async parallel delegation)  
**Repo commit baseline:** `518aca1` (`origin/main`, fast-forward pulled)

## 0. Honesty & Verification Ground Rules
- Inherit every binding rule of `AGENTS.md`: nothing is marked `checked` without a machine-verified proof (no `sorry`, no extra axioms beyond `propext`/`Classical.choice`/`Quot.sound`, no `native_decide`).
- Conditional results keep their exact hypothesis (`ERH`/`GRH`/`Grand RH`/`WEH`).
- Agents do **not** run git commits/pushes/PRs and do **not** close GitHub issues; they lease via `attack/desk/desk.py next --id <id>`, comment start/findings on the corresponding GitHub issue (`#2`–`#12`), write checkpoints + analysis + scratch experiments, and release honestly.
- Parent re-verifies every script, calculation, and Lean candidate before updating `attack/map/*`, `attack/JOURNAL.md`, `attack/failures.md`, and `attack/site/build.py`.

## 1. Current Baseline (Post-Pull)
- **Checked ground (11 claims):** `GB-DEFS`, `GB-FINITE-10000`, `GB-H1-CERT`, `GB-H1-CONSTS`, `GB-H1-CORE`, `GB-DYADIC`, `GB-B017`, `GB-B013-PART`, `GB-PSI-THETA`, `GB-B011-PHASE`, `GB-B010-L2`.
- **Audited but still OPEN (4 blockers):** `B-002` (#2), `B-003` (#3), `B-010` (#7), `B-011` (#8).
- **Unaudited & OPEN (7 blockers):** `B-004` (#4), `B-005` (#5), `B-007` (#6), `B-012` (#9), `B-013` (#10), `B-014` (#11), `B-015` (#12).
- **Stalled (1 blocker):** `B-016` (verify original `lean/` v4.16.0 build + `#print axioms`) — **executable immediately on this machine** (v4.16.0 + `.lake` present).
- **Toolchain note:** `lean/` uses `v4.16.0` (built locally); `attack/lean/` pins `v4.36.0` (not installed locally yet — check/handle cleanly without false verdicts).

## 2. Multi-Wave Execution Plan

### Wave 0 (Parent — Immediate)
- Refresh arXiv news monitor (`attack/news/monitor.py once` — done: 0 new).
- Resolve `B-016`: run `lake build` and capture exact `#print axioms` output for `WeakGoldbach.weak_goldbach_theorem`, `WeakGoldbach.binary_goldbach_exceptional_bound`, and `WeakGoldbach.binary_goldbach_density_one`; log to `attack/checker/runs.jsonl` and update `attack/map/`.

### Wave 1 (5 Parallel `gpt-6.2-astra` Agents — Disjoint Blockers & Files)
Each agent works one active frontier of Strong Goldbach under ERH/GRH/sieve/spectral methods, combining (a) deep mathematical attack seeking genuinely new signed/two-input bounds or sharp obstruction proofs, (b) reproducible numerical experiments in Python testing genuine primes against the synthetic countermodels, and (c) concrete formalizable micro-lemma specifications:

| Agent | Blocker(s) | GitHub Issue(s) | Primary Mathematical Target | Output Files |
|---|---|---|---|---|
| `astra-b002` | `B-002` | `#2` | Theorem 3 H3 centering (`U_N = sum (h^+)^2 - sum (h^-)^2`), H1/H2/H3 signed minor-arc criteria, multi-frequency / shifted-center averaging routes | `attack/agents/CHECKPOINT_B-002.md`, `attack/audit/B002_ASTRA_CENTERING_ATTACK.md` |
| `astra-b004` | `B-004`, `B-014` | `#4`, `#11` | GWX 2/2 ratios, `q^(1-2eta)` barrier, exact subtraction `(2)`, isolated `2^k`/`2p^2` identities `(11)`/`(16)`, Bettin–Chandee `17/33` repair vs `theta>2`, moving-line criterion `(7)`, merge decision `B-014 -> B-004` | `attack/agents/CHECKPOINT_B-004.md`, `attack/audit/B004_B014_GWX_RATIOS_ATTACK.md` |
| `astra-b012` | `B-012` | `#9` | Bilinear test with strict domination `B <= (1-c)S` for genuine shifted `Lambda(N-m)` vs parity model `a^+` (`B^+/U^+ = 1`); numerical `B/U` measurements on cube-root-rough & Vaughan Type II ranges; non-multiplicative reflected-coordinate observables | `attack/agents/CHECKPOINT_B-012.md`, `attack/audit/B012_BILINEAR_PARITY_ATTACK.md` |
| `astra-b013` | `B-013` | `#10` | Fourier reflection hole in `Z/MZ` (verify Fourier-smallness `O(sqrt(M log M))`) and largest-conductor reflection holes on `N=2^k` and `N=2p^2`; analyze multi-center / signed-energy / higher-order bypasses | `attack/agents/CHECKPOINT_B-013.md`, `attack/audit/B013_REFLECTION_HOLE_ATTACK.md` |
| `astra-b015` | `B-015`, `B-005` | `#12`, `#5` | Automorphic-RH parity survival `(7)`, subcritical `z=N^(2/9)` marked-divisor reduction `H(N)` `(8)`, Chen bias `B_C(N)` `(9)`, Li–Liu `(1+1.9)` narrowing `(13)-(15)`, numerical test of `H(N)` and `B_C(N)` for genuine primes vs `a^+` | `attack/agents/CHECKPOINT_B-015.md`, `attack/audit/B015_B005_SIEVE_NARROWING_ATTACK.md` |

### Wave 2 (Parent Re-Verification + Targeted Follow-Up)
1. **Parent re-verification**: independently run every Python test script, verify algebraic derivations and numerical margins, check banned tokens and desk lease hygiene.
2. **Map & dashboard update**: update `attack/map/claims.json`, `attack/map/blockers.json`, `attack/map/feed.jsonl`, `attack/JOURNAL.md`, `attack/failures.md`, and run `python3 attack/site/build.py`.
3. **Wave 2 Astra dispatch**:
   - Follow up on the highest-leverage mathematical opening(s) discovered in Wave 1 (or synthesize cross-blocker obstructions/bypasses across `B-002`/`B-004`/`B-012`/`B-013`/`B-015`).
   - Attack `B-007` (#6) computational verification design/benchmark on a modest bounded range (without running multi-hour exhaustive runs).
   - Kernel-check the newly proposed combinatorial/algebraic micro-lemmas (e.g., H3 centering identity `U_N = sum (h^+)^2 - sum (h^-)^2`, rough-set detector decomposition `2 P = S - Q - B`, largest-conductor reflection-hole witness on `Z/8Z` or `Z/16Z`, and `K_0^{-1} = S(N)` prime-by-prime local factor identity).
