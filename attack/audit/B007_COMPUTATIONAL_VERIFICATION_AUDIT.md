# B-007 · Independent finite Goldbach verification

**[I] Verdict, 27 November 2026.** Keep B-007 open. The strongest new contiguous native run here reaches **50,000,000**. The new Lean 4.16 certificate reaches **10,000**, the existing map frontier. The stored prime ladder passes a full independent arithmetic replay. Applying that ladder to reach the ternary bound of 10²² still requires the binary input through 4 × 10¹⁸. [Issue #6](https://github.com/nisbenz/goldbach-grh-lean/issues/6)

[Q] Tags govern the paragraph, table or code block they introduce. [Q] denotes a repository statement or source observation, [P] a computation run here or a mathematical deduction shown here, [I] an interpretation, design or conditional budget, and [U] an external input or outstanding result. A native PASS and a Lean kernel replay have different evidence. The formal submission checker returned a module-layout rejection for the scratch prototype, recorded below.

## Bounded native measurements

[P] Host measurements used a 13th Gen Intel Core i5-13400F, one socket, 10 physical cores, 16 logical processors reported by `nproc`, an AMD Radeon RX 6750 XT (`gfx1031`), and GCC 16.2.1. A Python parent took the difference of two `time.perf_counter_ns()` readings around the entire subprocess, including startup, sieve, worker joins, reporting and exit. Every benchmark used a 16-second SIGKILL guard. The times below are observed elapsed durations. Compiler time is excluded from executable throughput.

[P] The fresh binary was built with `g++ -O3 -std=c++17 -pthread verify/verify_finite.cpp -o /tmp/astra_w2_b007/verify_finite` and invoked with **both positional bounds** set to 50000000, so only its binary phase ran. It counted 24,999,999 evens, exactly 50,000,000/2 − 1, in **0.091652351 s**, or **272,769,860.54 evens/s**. The maximum least prime summand was **1,039**. A different wheel implementation found its first occurrence at 37,998,938. An additional trial-division loop over all candidates from 2 through 1,039 at that input found precisely the pair 1,039 + 37,997,899.

[P] The second implementation packs residues 1, 7, 11, 13, 17, 19, 23 and 29 into a byte per 30 integers. It treats 2, 3 and 5 separately, sieves through the integer square root of the window's upper endpoint, and queries a left halo for complements. It tries sorted primes through 8,191 and explicitly counts every miss. All the tested windows had zero misses. The CPU and HIP paths share that wheel and witness routine. The repository's odd-bit implementation is a separate algorithm. The HIP timing includes the CPU sieve, device startup, input transfers, the kernel, result copy and host aggregation.

[P] The two test domains and independent executions gave the following results. The high window is exactly [99,999,992,000,002, 100,000,000,000,000]. No intervening range is implied.

| Domain and implementation | Evens | Wall seconds | Millions of evens/s | Max least prime | Sum of least primes |
|---|---:|---:|---:|---:|---:|
| Prefix to 50,000,000, repository C++ | 24,999,999 | 0.091652351 | 272.770 | 1,039 | unreported |
| Same prefix, 30-wheel CPU | 24,999,999 | 0.208484877 | 119.913 | 1,039 | 714,487,162 |
| Same prefix, 30-wheel HIP | 24,999,999 | 0.429254424 | 58.241 | 1,039 | 714,487,162 |
| High window, 30-wheel CPU | 4,000,000 | 0.113785109 | 35.154 | 2,131 | 275,333,378 |
| High window, 30-wheel HIP, median of three synchronized repeats | 4,000,000 | 0.114441361 | 34.952 | 2,131 | 275,333,378 |

[P] Ordered 64-bit witness checksums matched across CPU and GPU, `a36598bfa3c32046` for the prefix and `2534ffa86f63f522` for the high window. The first high-window maximum occurred at 99,999,996,372,854. The first high-window GPU attempt exited on signal 11. A retry with `HIP_LAUNCH_BLOCKING=1` took 0.114330551 s, followed by repeats at 0.117979904, 0.114441361 and 0.113535306 s. The cause of the crash is undiagnosed. The failed attempt contributes zero coverage. [I] These short host-sieved GPU measurements do not establish a device-resident throughput or reliability rate.

## Audit of the native binary and ladder

- [Q/P] **Encoding and sieve.** In `OddSieve`, bit index k represents 2k+1. The word is k/64 and the shift is k mod 64, so every shift is in [0,63]. Clearing the initial vector means “unmarked.” Marking k=0 excludes 1, and the query separately handles 2, small values and evens. The constructor allocates ⌈(⌊M/2⌋+1)/64⌉ words. With even M it includes an extra odd slot at M+1, whose primality can be wrong (e.g. 49 at M=48). All legitimate queries in the search are ≤M. The stored `limit` never enforces this precondition.
- [P] For each unmarked odd i with i²≤M, marking index (i²−1)/2 onward in strides of i crosses out odd multiples i², i²+2i, …. Every odd composite ≤M has a least prime divisor ≤√M, so it is marked. For the intended sizes the square and index arithmetic fit. The generic `u64` interface would need `i <= M/i` or a wide product near its maximum. The allocation formula itself uses at most half the numeric range before word rounding. Memory allocation, representability in `size_t`, and successful thread creation are practical preconditions. The exact monolithic bit vector alone at 4 × 10¹⁸ would use **250,000,000,000,000,008 bytes**.
- [Q/P] **Every even and its minimal witness.** The counter starts at one for 4=2+2. Workers fetch even starts 6+2,000,000j and cover through min(M,start+1,999,998), inclusive, in steps of two. With no wrap these intervals are disjoint and consecutive. For E≥6 both summands must be odd. Sorted primes up to min(M,200,000) are tried up to E/2. On exhausting them, the fallback scans all odd integers above that cap through E/2 and tests both summands. The cap is even after M is rounded, so cap+1 has the right parity. The source comment mentioning 100,000 understates the actual cap. A bound on the smallest summand is unnecessary for correctness. A success counter equality check at exit would help catch future partition regressions.
- [Q/P] **Parallelism.** Sieve and candidate vector are initialized before spawning and remain read-only. Unique chunk allocation, totals and failure state are atomic. Each worker accumulates a private count and maximum, then merges the maximum by compare/exchange. The final reads follow all joins. Relaxed loads permit extra work after a failure, and a failing worker can omit its local counts. The process returns failure before publishing a PASS in that branch. The mutex serializes error output. Hardware concurrency can be zero, for which the code selects one thread. This build succeeded through transitive headers for `std::min/max`; portable source should include `<algorithm>` explicitly.
- [Q/P] **Miller–Rabin.** Trial division handles 2 through 37 and their multiples. For remaining odd n, write n−1=2ˢd, d odd. Modular exponentiation accepts 1 or −1 initially, or −1 at one of the following s−1 squarings, for each base reduced modulo n. A base divisible by n is skipped. Multiplication casts to unsigned 128 bits **before** multiplying two unsigned 64-bit operands, so the product fits, and reduction occurs before narrowing. The modulus is positive on this path. The seven bases are 2, 325, 9375, 28178, 450775, 9780504 and 1795265022. [U] The exactness of that base set for n<2⁶⁴ and its Sinclair (2011) attribution are external. The binary sieve has no dependency on that theorem.
- [P] **Ladder coverage.** Assume an even binary bound M, an odd prime first rung ≤M−4, strictly increasing odd prime rungs with gaps ≤M−4, and a last rung ≥L−4. For odd 7≤N≤M+3 take N−3. Beyond that range take the largest rung pᵢ≤N−4. If this is the last, equality follows from the endpoint. Otherwise N−4<pᵢ₊₁, so 4≤N−pᵢ<4+(pᵢ₊₁−pᵢ)≤M. The difference is even. An overshoot of L by the final rung is allowed. The C++ builder greedily tests candidates below cur+M−4 and rejects a failure to make progress. This construction extends a **ternary** range.
- [P] **Reproduced false PASS.** Running the fresh binary with `6 99` yielded `p_k = 18446744073709551557` and printed “1 ladder primes from p_0 <= 2” and PASS. The downward unsigned first-rung search steps from 1 to 2⁶⁴−1. It finds a large prime outside the admissible interval. M=4 also permits initial subtraction from zero. With rounded M<4 the program counts 4 outside its interval and M−4 can underflow. [I] Validate M≥4 for binary-only runs, and require M−4≥3 and an actual odd first rung when the ladder is needed. Check the first bound explicitly and terminate downward searches before underflow.
- [Q/P] **Other input and arithmetic boundaries.** The command uses `strtoull` without checking end pointer, errno, sign or extra arguments. Odd M is rounded *up*, and UINT64_MAX wraps at that step. The advertised L≤2⁶³−1 is unenforced. M+3, chunk-end addition, E+=2, the fetch-add cursor and cur+max_step can wrap near the unsigned limit. These are separate from the correctly widened modular multiplication. Require checked arithmetic or enforce the intended safe input domain and allocation budget. An error finding a next rung only invalidates this ladder construction.

## Audit and replay of the Python Pratt ladder

[Q/P] The command-line script **generates** a ladder and optionally writes JSON. It has no input-file replay mode. Its 12-base probable-prime filter, deterministic-seeded Pollard rho and primitive-root search are generator heuristics. A difficult factorization or pseudoprime can cause unbounded retries. For well-formed integer trees the verifier instead checks the complete factorization of p−1 with positive exponents, a matching recursive prime proof for each distinct factor other than 2, and the power congruences for g. The Fermat equality makes g a unit. Its order divides p−1, and cannot divide (p−1)/q for any prime factor q. Hence its order is p−1, which is ≤φ(p). For p>1 this forces p prime. This argument justifies the script's inequality-to-one check even for a composite candidate modulus. Python integer powers use exact arithmetic.

[Q/P] The shared `verified` set can reuse a previously validated integer prime even if a later duplicate subtree differs. It certifies numbers, and need not authenticate every duplicate encoding. Built-in `assert` guards almost the entire verification pass. Running the generator with `python -O` skips even its call to `verify_pratt_cert`. The in-memory arrays grow together, but a standalone reader must check lengths before `zip`, tie each certificate to its expected prime, test every rung's parity, and independently validate metadata. The internal decoder coerces factors and exponents with `int` and assumes a sane schema. A production reader should reject malformed/nonintegral values, noncanonical keys and unreasonable input sizes. Scientific-notation CLI arguments pass through a binary float and can round. Use full integer decimal targets. The generator's early return when N0≤B+3 uses the supplied binary premise. Small B can leave no odd first rung.

[P] The original CLI on B=10,000, N0=1,000,000 built and checked 101 rungs in 0.025136513 s. Separately, the stored plain and decompressed JSON matched byte for byte (SHA-256 `ef6c41c54bdcdf377b0f387d70a0eae87f211aa8c3ac995f451dcc40c2ceb593`). In **0.922122976 s**, the scratch reader checked the supplied B=4×10¹⁸ and N0=10²², lengths, endpoints, strict ordering, parity and every gap. It invoked the repository Pratt verifier, then independently traversed **all 86,507 stored nodes** without memoization, checking gcd(g^((p−1)/q)−1,p)=1 for each q as well as the full factor product and Fermat congruence. It found 2,501 rungs, first 3,999,999,999,999,999,887, last 10,003,999,999,999,999,876,777, smallest gap 3,999,999,999,999,999,640 and largest gap 3,999,999,999,999,999,996 = B−4. There were 13,198 distinct primes including 2. The repository cache contained 13,197 because its factor-2 branch needs no recursive call. These checks authenticate the supplied ladder for the stated binary premise.

## Distributed budget through 4 × 10¹⁸

[P] An even upper bound X≥4 has C(X)=X/2−1 targets. At 4 × 10¹⁸ the count is **1,999,999,999,999,999,999**. For sustained end-to-end rate r evens/s per node, D complete passes, K nodes and productive fraction u, the exact model has time D·C(X)/(K·u·r) seconds. A deadline T needs ⌈D·C(X)/(u·r·T)⌉ nodes. A year below is 31,557,600 seconds. These equations allow exact budgets once the sustained rate and utilization are specified.

[I] The table projects measured *whole-node* rates or an explicitly hypothetical GPU rate. Displayed times are rounded. No measurement at the full-range endpoint exists here. The first row assumes the exceptionally fast low prefix remains representative. The wheel rows use the four-million-even pilot near 10¹⁴, including rebuilding its base and shipping GPU data. Device-resident sieving and persistent workers could improve those rates. Sieving to √X, memory bandwidth, larger least summands, sparse outliers, distributed retries and accounting can reduce them. A CPU-node-year here represents the entire 16-logical-processor host.

| Per-node rate used | 1-pass years, 1 node | Nodes for 2 passes in 1 year at 80% | Years for 2 passes on 100 nodes at 80% |
|---|---:|---:|---:|
| Native low prefix, 272.770 million/s | 232.34 | 581 | 5.81 |
| Segmented 30-wheel CPU pilot, 35.154 million/s | 1,802.82 | 4,508 | 45.07 |
| Segmented host-sieved Radeon pilot, 34.952 million/s | 1,813.21 | 4,534 | 45.33 |
| Hypothetical device-resident GPU, 1 billion/s | 63.38 | 159 | 1.58 |

[I] With one CPU pass and one independent GPU pass at the two wheel rates, a one-year deadline at 80% utilization calls for 2,254 CPU nodes and 2,267 GPU-equipped nodes. Identical binaries on many machines share software errors. Independent implementations, disjoint accounting and recomputation of discrepancies matter as much as replication.

[I] At the measured high-window CPU rate, **10¹⁰** models at 2.37 minutes, **10¹²** at 3.95 hours, and **10¹⁴** at 395.09 hours (16.46 days), one complete pass on one node at 100% utilization. A local 10¹⁰ end-to-end segmentation run is a manageable next budget, 10¹² is a plausible overnight-scale replication, and 10¹⁴ is a sustained community milestone. Each needs explicit compute authorization. Only the 50-million prefix and the stated high window were run in this audit. [U] The historical computational result to 4 × 10¹⁸ remains external to this experiment. [Oliveira e Silva, Herzog and Pardi](https://sweet.ua.pt/tos/goldbach.html)

[I] **Worker layout.** Partition the integer line into aligned half-open intervals [jW,(j+1)W), W=30·2²⁴=503,316,480, and intersect each with [4,X+1). This gives 7,947,285,971 nonempty tiles at full X. Generate all base primes to ⌊√X⌋=2,000,000,000. For a moving window, mask nonprime wheel candidates beginning at the first multiple ≥max(p²,left), with wide endpoint arithmetic. Keep the small primes themselves eligible. Bucket distant strikes to avoid rescanning every base prime in every tile. Carry a left halo H=65,535 for n−p. Sweep small prime shifts in increasing order, remove newly witnessed evens from a pending bitmap, and record first-hit counts or a digest of first witnesses. Handle 4 specially. A miss requests wider halos or an exact primality-witness search through n/2. Exhaustion of the fast-path cap is an unfinished input, never a refutation or a successful tile. Certifying minimality requires excluding *all* smaller candidates, whereas one valid pair certifies the existential theorem.

[P/I] A floor-quotient Eratosthenes prime count gave π(2,000,000,000)=98,222,287 in the bounded budget calculation. It starts with S(v)=v−1; on each surviving p, in decreasing order of quotient v≥p² subtract S(⌊v/p⌋)−S(p−1). This removes exactly the survivors whose least factor is p. It counts base primes without searching Goldbach pairs. For the proposed uncompressed layout the following payload sizes are exact under the stated conventions.

| Per-worker payload | Bytes |
|---|---:|
| Shared base primes as unsigned 32-bit integers | 392,889,148 |
| One unsigned 64-bit strike cursor per base prime | 785,778,296 |
| 30-wheel bitmap, W/30 + ⌈H/30⌉ bytes | 16,779,401 |
| One pending bit for each even, W/16 bytes | 31,457,280 |
| Total for one worker | **1,226,904,125** |

[I] Two wheel/pending buffers add 48,236,681 bytes. Sixteen workers that share only the prime list need 13,737,128,780 bytes of these payloads. Account separately for bucket links, wheel phases, outliers, output buffers, process memory and driver reservations. A GPU worker can keep the base list and cursors resident, produce masks on device, and return tile counters, hashes and exceptional witnesses. The HIP pilot used a host sieve, copied full 16-bit witnesses back, and used small pilot windows. [U] The two GPU papers in the local news feed describe segmented double sieving and device-resident scheduling. Their performance and correctness claims were not independently verified or used as measured rates. [GoldbachGPU, arXiv:2603.02621](https://arxiv.org/abs/2603.02621) · [GPU-resident architecture, arXiv:2603.07850](https://arxiv.org/abs/2603.07850)

[I] **Independent coverage.** A manifest should bind mathematical endpoints, even count, code/configuration identity, base-prime generation, exceptional inputs, witness digest and status. Seal a tile only when every expected even has a witness and both passes agree after any discrepancies are resolved. Sort manifests by tile index and check contiguous endpoints, exact total, duplicates and no pending evens. Retry idempotently under the same tile identity. A 64-byte summary per tile alone uses 508,626,302,144 bytes. A one-byte code per even would take approximately 2 exabytes and require a separate encoding for overflow. Neither aggregate counters nor hashes are Lean proofs. At full scale, recomputable chunks with a proved checker are much more attractive than publishing every witness pair.

## Lean 4.16 certificate and independent kernel replay

[Q] The existing generator builds an ordinary byte sieve, stores the first pair for each even, splits on half the even using `interval_cases`, and emits two `norm_num [Nat.prime_def_lt]` proofs plus an addition proof per case. Its `int(n ** 0.5)` uses floating-point arithmetic, which is unnecessary and could miss a divisor on large inputs. Generation also stores the dictionary of pairs and the source lines. Wrong generated witnesses should fail kernel checking. Even the generator's “bytes” print counts Python characters rather than UTF-8 bytes. The failure log records two server restarts that killed the 2.58 MB, roughly 25,000-witness build for 50,000. [I] Large case splits and repeated primality elaboration make a restart costly. The log establishes interruption, with no evidence of a proof error, an out-of-memory kill, or an intrinsic Lean size limit. [Generator](../src/gen_cert.py) · [Failure log](../failures.md)

[P] The prototype copied `Goldbach/Basic.lean` byte-for-byte into scratch and compiled it against the cached Mathlib for Lean 4.16.0, commit `128a1e6b0a82`. Both the generator and its sieve can be untrusted. The kernel checks these three obligations.

1. [P] For a band ending at b, let R=⌊√b⌋ and supply an integer D whose intended factors are the primes in that band. Prove once by kernel reduction that gcd(D,R!)=1. To certify n in the band, check 2≤n≤b and D mod n=0. Any divisor d with 2≤d≤√n would divide both D and R!, hence their gcd 1. The Mathlib characterization `Nat.prime_def_le_sqrt` gives `Nat.Prime n`. Missing factors of D can lose coverage but cannot introduce a composite certificate. The initial cases are 2 and 3. Later bands [4,15], [16,255] and [256,b] cover this benchmark. The upper-bound and coprimality conditions are checked separately for every band.
2. [P] For each even, the data contain just p. The checker tests p≤n and marks both p and n−p using the validated bands. Groups of 32 witnesses are packed into natural-number digits, using radix 128 at B=2,000 and 256 at B=10,000. Processing a digit uses remainder and division, then advances n by 2. The inductive Lean lemma constructs the existential witnesses, including the addition equality. Every digit, including padding, is checked. The final block at B=10,000 reaches 10,050. The exported theorem states exactly the requested bound.
3. [P] The length proof and block soundness lemma imply coverage of every even n in the original `GoldbachAttack.BinaryGoldbachUpTo B`. The generated theorem uses `by decide +kernel` for Boolean and arithmetic checks. No compiled Boolean oracle is in the proof. A second scratch program reads the actual object files, replays the project declarations into a fresh Mathlib environment using Lean 4.16's `Environment.replay`, requires the named declaration to be a theorem, and asks the kernel to use it at the externally constructed type `GoldbachAttack.BinaryGoldbachUpTo B`. The project source scan found no banned declaration or tactic tokens. Both positive axiom audits printed exactly `[propext, Classical.choice, Quot.sound]`.

[P] Final source-build timings include Lean startup and cached dependency loading. Compiling the identical definitions file took 1.885442432 s separately and the final reusable `Blocks.lean` took 2.173609781 s separately. At 10,000 the bound-specific source is 15,605 bytes, plus 2,438 shared bytes, compared with the repository's 511,737-byte monolithic source. The final 10,000-specific object is 359,208 bytes; the shared object is 307,768 bytes.

| Bound | Existing generator on this host | Packed certificate on this host | Exact-type kernel replay |
|---:|---:|---:|---:|
| 400 | 6.258555371 s | 2.041691138 s | outside replay benchmark |
| 2,000 | 16 s deadline reached | 2.591409618 s | 2.599328169 s, 131 constants in replay set |
| 10,000 | historical map reports 95 s on another setup [Q] | 5.508629926 s | 5.380948840 s, 381 constants in replay set |

[P] The matched, completed 400 comparison gives **3.07×**. At 2,000 the legacy build was still running at the cutoff, giving a **greater than 6.17×** lower bound on its time relative to the packed bound-specific build. The historical 95 s divided by 5.509 s is about 17.25, with different environments and build commands. This is not a matched speed measurement. Final successful 10,000 build output and independent replay output follow.

```text
'GoldbachAttack.binaryGoldbachUpTo_10000' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS GoldbachAttack.binaryGoldbachUpTo_10000 : GoldbachAttack.BinaryGoldbachUpTo 10000; replay set 381 constants
```

[P] A negative control changed the first witness for 4 to 4, making its complement 0. The kernel tactic reported that `Packed.blocks … = true` **is false**, Lean returned exit 1, and no negative-control object was produced. An earlier single-loop trial-division implementation timed out with ordinary elaborator reduction. Its kernel-reduction version passed at 2,000 in 9.591241861 s. Packing consecutive digits and amortizing primality across products reduced that bound-specific time to 2.591409618 s.

[P] **Repository gate.** A byte-for-byte scratch copy of the standard wrapper ran the unmodified vendored checker with the statement `GoldbachAttack.BinaryGoldbachUpTo 10000`. The wrapper log stayed in scratch. The checker rejected the scratch path before examining its mathematics. The exact lines were:

```text
REJECTED (not-a-project-module): /tmp/astra_w2_b007/Block10000.lean is not a module of PEqualNP or CheckerSuite under lean/
STRICT VERDICT: REJECTED (exit 1; vendored check-lean.mjs, Apache 2.0)
```

[I] The positive exact-type replay above is a Lean kernel result. The scratch prototype has no repository acceptance or claim-status change. A future integrated checker can bind module names and the expected Goldbach definitions while retaining the exact-type and axiom checks.

[I] **Scaling the Lean design.** Using 1.89 s as an approximate fixed import cost and the remaining 3.62 s at 10,000 as variable work, a constant-cost-per-target model gives roughly **38 s at 10⁵** and **6.1 minutes at 10⁶**. If growing a single product also makes each remainder cost proportional to bound, a quadratic-variable-work scenario gives **6.1 minutes** and **10.1 hours**, respectively. These scenarios are neither measurements nor upper bounds. The last product already grew from 2,530 bits at 2,000 to 13,996 bits at 10,000. Actual scaling changes at band boundaries and depends on kernel reductions, source elaboration and memory. No Lean benchmark above 10,000 was run.

[I] For larger bounds, keep product pages of bounded bit length, with a kernel-checked gcd against the square-root factorial for that page's maximum. Bind a page index/range to each membership lookup. Check consecutive target chunks in separate modules, prove an interval-gluing theorem and combine neighboring intervals in a balanced tree. The root must check exact endpoints and the defining predicate. A verified wheel-sieve backend could instead prove every asserted prime flag sound once per segment, including its halo. Its proof needs complete base-prime coverage through the integer square root, strike alignment, prime exceptions, bit indexing and the implication from a surviving flag to primality. Digit decoding and endpoint gluing can be reused. No full-range Lean throughput follows from this prototype. The factorial certificate is designed for moderate bounds, not R=2 billion.

## Reproduction material

[P] The scratch directory is `/tmp/astra_w2_b007/`. The handoff includes the source of the proof, generators and independent checks below so the experiment survives loss of that directory. For the Lean runs, copy `attack/lean/Goldbach/Basic.lean` unchanged to `Goldbach/Basic.lean` in scratch. Use the local 4.16 toolchain and the absolute dependency paths from `lake env printenv LEAN_PATH` in the repository's top-level `lean/` directory. The timing wrapper, Lean launcher and recipes below encode the same bounds as the runs. SHA-256 of the definitions source is `742896942a43293f2a8689df8adeb44d8a347680e2a7593d4d491a4278707678`. SHA-256 of `verify_finite.cpp` is `79d1a8442a4f7f4394990bf062fa033a68f6d36e5e0d8648afd45158d0f648b1` and of `verify_ladder.py` is `b431bd60f75320f08f679478bac1a5d3a60ea559abf1ff9c7582570020ee156f`.

```bash
# In /tmp/astra_w2_b007 with the extracted sources and identical Basic.lean
python3 run.py ./lean-run -o Goldbach/Basic.olean Goldbach/Basic.lean
python3 run.py ./lean-run -o Blocks.olean Blocks.lean
python3 genblocks.py 10000
python3 run.py ./lean-run -o Block10000.olean Block10000.lean
python3 run.py ./lean-run --run Recheck.lean 10000
python3 run.py python3 -B replay.py
python3 run.py python3 budget.py
timeout -s KILL 16 /opt/rocm/bin/hipcc -O3 -std=c++17 --offload-arch=gfx1031 wheel.hip -o wheel
python3 run.py ./wheel prefix cpu
python3 run.py env HIP_LAUNCH_BLOCKING=1 ./wheel window gpu
```

<details>
<summary>[P] Blocks.lean</summary>

SHA-256 `4d44427d0e3fd23bdf8abc2db036308d64f2b1710284a28181f733fedecda3ee`.

```lean
import Goldbach.Basic

namespace GoldbachAttack.Packed

theorem primeOfProduct {D R n : Nat} (hc : Nat.gcd D R.factorial = 1)
    (h : 2 ≤ n) (hs : n.sqrt ≤ R) (hp : D % n = 0) : Nat.Prime n := by
  refine Nat.prime_def_le_sqrt.mpr ⟨h, ?_⟩
  intro d hd hds hdn
  have dv := Nat.dvd_gcd (hdn.trans (Nat.dvd_of_mod_eq_zero hp))
    (Nat.dvd_factorial (by omega : 0 < d) (hds.trans hs))
  rw [hc, Nat.dvd_one] at dv
  omega

private def HasPair (n : Nat) : Prop :=
  ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

def block (mark : Nat → Bool) (base : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k+1, n, data =>
    let p := data % base
    decide (p ≤ n) && mark p && mark (n-p) && block mark base k (n+2) (data/base)

private theorem block_sound {mark base k n data} (s : ∀ x, mark x = true → Nat.Prime x)
    (h : block mark base k n data = true) : ∀ i < k, HasPair (n+2*i) := by
  induction k generalizing n data with
  | zero => omega
  | succ k ih =>
    simp only [block, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      exact ⟨_, _, s _ h.1.1.2, s _ h.1.2, by omega⟩
    | succ i =>
      have t := ih h.2 i (by omega)
      convert t using 1
      omega

def blocks (mark : Nat → Bool) (base width : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | w::ws, n => block mark base width n w && blocks mark base width ws (n+2*width)

private theorem blocks_sound {mark base width ws n} (s : ∀ x, mark x = true → Nat.Prime x)
    (h : blocks mark base width ws n = true) : ∀ i < ws.length * width, HasPair (n+2*i) := by
  induction ws generalizing n with
  | nil => simp
  | cons w ws ih =>
    simp only [blocks, Bool.and_eq_true] at h
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    intro i hi
    by_cases first : i < width
    · exact block_sound s h.1 i first
    · have t := ih h.2 (i-width) (by omega)
      convert t using 1
      omega

theorem certified (B base width : Nat) (ws : List Nat) (mark : Nat → Bool)
    (sound : ∀ x, mark x = true → Nat.Prime x)
    (hlen : B/2-1 ≤ ws.length * width) (h : blocks mark base width ws 4 = true) :
    BinaryGoldbachUpTo B := by
  intro n hn hB he
  obtain ⟨k, rfl⟩ := he
  have t := blocks_sound sound h (k-2) (by omega)
  have e : 4+2*(k-2) = k+k := by omega
  exact e ▸ t

end GoldbachAttack.Packed
```

</details>

<details>
<summary>[P] genblocks.py</summary>

SHA-256 `f37f39f114c0d1c77718dbb19a53cf3aca14166f6c9047d14be6c42d886a1ecc`.

```python
import sys
from pathlib import Path
from math import isqrt,prod
B=int(sys.argv[1])
W=32
U=((B//2-1+W-1)//W)*2*W+2
prime=bytearray([1])*(U+1)
prime[:2]=bytes(2)
for i in range(2,isqrt(U)+1):
    if prime[i]:
        prime[i*i::i]=bytes((U-i*i)//i+1)
ps=[n for n in range(2,U+1) if prime[n]]
picks=[next(p for p in ps if p<=n//2 and prime[n-p]) for n in range(4,U+1,2)]
base=1 << max(picks).bit_length()
words=[sum(v*base**j for j,v in enumerate(picks[i:i+W])) for i in range(0,len(picks),W)]
ds=[]
bands=[3,15,255]
while (bands[-1]+1)**2-1<U:
    bands.append((bands[-1]+1)**2-1)
bands.append(U)
src=['import Blocks','namespace GoldbachAttack','set_option maxRecDepth 100000','set_option maxHeartbeats 20000000',f'private def witnesses : List Nat := [{",".join(map(hex,words))}]']
for i,b in enumerate(bands[1:]):
    d=prod(n for n in ps if bands[i]<n<=b)
    src += [f'private def D{i} : Nat := {hex(d)}',f'private theorem cop{i} : Nat.gcd D{i} (Nat.factorial {isqrt(b)}) = 1 := by decide +kernel']
mark='if n ≤ 3 then true else '
for i,b in enumerate(bands[1:-1]):
    mark+=f'if n ≤ {b} then decide (D{i} % n = 0) else '
mark+=f'decide (n ≤ {U} ∧ D{len(bands)-2} % n = 0)'
src += [f'private def mark (n : Nat) : Bool := decide (2 ≤ n) && ({mark})','private theorem sound (n : Nat) (h : mark n = true) : Nat.Prime n := by','  simp only [mark, Bool.and_eq_true, decide_eq_true_eq] at h','  obtain ⟨lo, v⟩ := h','  split at v','  · interval_cases n <;> decide']
indent='  '
for i in range(len(bands)-2):
    src += [indent+'· split at v',indent+'  · rename_i hi',indent+f'    exact Packed.primeOfProduct cop{i} lo ((Nat.sqrt_le_sqrt hi).trans (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by decide)))) (of_decide_eq_true v)']
    indent+='  '
src += [indent+'· obtain ⟨hi, rem⟩ := of_decide_eq_true v',indent+f'  exact Packed.primeOfProduct cop{len(bands)-2} lo ((Nat.sqrt_le_sqrt hi).trans (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by decide)))) rem',f'theorem binaryGoldbachUpTo_{B} : BinaryGoldbachUpTo {B} :=',f'  Packed.certified {B} {base} {W} witnesses mark sound (by decide +kernel) (by decide +kernel)',f'#print axioms binaryGoldbachUpTo_{B}','end GoldbachAttack']
Path(f'Block{B}.lean').write_text('\n'.join(src)+'\n')
```

</details>

<details>
<summary>[P] Recheck.lean</summary>

SHA-256 `35798a80b16f5b491350df4415fc45042ea52aaf9e32f6df148246bedf12d8d0`.

```lean
import Lean.Replay
import Lean.Util.Path

open Lean
def main (args : List String) : IO Unit := do
  let [bound] := args | throw (IO.userError "expected bound")
  let some b := bound.toNat? | throw (IO.userError "expected a natural number")
  initSearchPath (← findSysroot)
  let base ← importModules #[{ module := `Mathlib }] {}
  let mut cs : Std.HashMap Name ConstantInfo := {}
  for m in ["Goldbach.Basic", "Blocks", "Block" ++ bound] do
    let (data, _) ← readModuleData (← findOLean m.toName)
    for ci in data.constants do
      cs := cs.insert ci.name ci
  let env ← Environment.replay cs base
  let name := ("GoldbachAttack.binaryGoldbachUpTo_" ++ bound).toName
  let some (.thmInfo _) := env.find? name | throw (IO.userError "missing theorem")
  let target := mkApp (mkConst `GoldbachAttack.BinaryGoldbachUpTo) (mkNatLit b)
  match env.addDecl {} (.thmDecl { name := `ExactReplay, levelParams := [], type := target, value := mkConst name }) with
  | .ok _ => IO.println s!"PASS {name} : GoldbachAttack.BinaryGoldbachUpTo {b}; replay set {cs.size} constants"
  | .error _ => throw (IO.userError "kernel rejected the recorded type")
```

</details>

<details>
<summary>[P] run.py</summary>

SHA-256 `f4622611225911d314b836d30fd5bd9fd7cb614bd7fc69bd8e4b3e4a14c38412`.

```python
import sys,time,subprocess,resource
start=time.perf_counter_ns()
r=subprocess.run(['timeout','-s','KILL','16',*sys.argv[1:]])
elapsed=time.perf_counter_ns()-start
print(f'wall_ns={elapsed} maxrss_KiB={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} exit={r.returncode}')
sys.exit(r.returncode)
```

</details>

<details>
<summary>[P] lean-run</summary>

SHA-256 `e163a2ce3f1712dee0b2e49e4ce98d5713a05ce13af5a0cddac3c4e266ea81c0`.

```bash
#!/bin/bash
set -eu
cd /tmp/astra_w2_b007
proj=/home/nisbenz/.t3/projects/weak-goldbach/lean
libpath=$(cd "$proj" && lake env printenv LEAN_PATH | tr : '\n' | while read -r path; do realpath -m "$path"; done | paste -sd:)
export LEAN_PATH="$PWD:$libpath"
exec lean +leanprover/lean4:v4.16.0 "$@"
```

</details>

<details>
<summary>[P] replay.py</summary>

SHA-256 `69583c6ee306c52254345e94e1c565c73af5fed65ab2f632a310c08f9f0f892f`.

```python
from pathlib import Path
from math import gcd, prod
import gzip, json, runpy, sys
V=Path('/home/nisbenz/.t3/projects/weak-goldbach/verify')
source=(V/'ladder_certs.json').read_bytes()
assert source == gzip.decompress((V/'ladder_certs.json.gz').read_bytes())
data=json.loads(source)
B=4*10**18
T=10**22
ps, trees = data['primes'],data['certificates']
assert (data['B'], data['N0'],data['max_step'])==(B,T,B-4)
assert len(ps)==len(trees)==data['rungs'] and len(ps)>0
assert ps[0]<=B-4 and ps[-1]>=T-4
gaps=[b-a for a,b in zip(ps,ps[1:])]
assert min(gaps)>0 and max(gaps)<=B-4
repo=runpy.run_path(str(V/'verify_ladder.py'))['verify_pratt_cert']
memo=set()
unique=set()
nodes=0
def tree_prime(n,tree):
    global nodes
    nodes+=1
    assert type(n) is int and n==tree['p'] and type(tree['p']) is int
    if n==2:
        unique.add(n)
        return
    assert n>=3 and n%2==1
    fac={int(q):e for q,e in tree['factors'].items()}
    assert all(q>=2 and type(e) is int and e>0 for q,e in fac.items())
    assert prod(q**e for q,e in fac.items())==n-1
    g=tree['g']
    assert type(g) is int and pow(g,n-1,n)==1
    for q in fac:
        if q!=2:
            tree_prime(q,tree['subcerts'][str(q)])
        else:
            unique.add(2)
        assert gcd(pow(g,(n-1)//q,n)-1,n)==1
    unique.add(n)
for p,tree in zip(ps,trees,strict=True):
    assert p%2==1 and p==tree['p'] and repo(tree,memo)
    tree_prime(p,tree)
assert memo|{2}==unique
print('rungs',len(ps),'first',ps[0],'last',ps[-1],'gap_min',min(gaps),'gap_max',max(gaps),'repo_cache',len(memo),'unique_including_2',len(unique),'visits',nodes)
```

</details>

<details>
<summary>[P] wheel.hip</summary>

SHA-256 `93cbab4d68925832b4ff42d9b3d6f34e6642ea124a32aa2b404355dc3bdf4753`.

```cpp
#include <hip/hip_runtime.h>
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <thread>
#include <vector>

using u64 = uint64_t;
using u16 = uint16_t;
using u8 = uint8_t;
constexpr unsigned cap = 8191;
using Clock = std::chrono::steady_clock;

__host__ __device__ int wheelbit(unsigned r) {
    switch(r) {
        case 1: return 0; case 7: return 1; case 11: return 2; case 13: return 3;
        case 17: return 4; case 19: return 5; case 23: return 6; case 29: return 7;
        default: return -1;
    }
}
__host__ __device__ u16 witness(u64 n, u64 firstBlock, const u8* bits, const u16* primes, unsigned np) {
    if (n==4) return 2;
    for(unsigned i=1; i<np; ++i) {
        const unsigned p=primes[i];
        if(2*p>n) break;
        const u64 q=n-p;
        const int k=wheelbit(q%30);
        if(q==3 || q==5 || (q>1 && k>=0 && (bits[q/30-firstBlock] & (1u<<k)))) return p;
    }
    return 0;
}
__global__ void search(u64 start,unsigned count,u64 firstBlock,const u8* bits,const u16* ps,unsigned np,u16* out) {
    unsigned i=blockIdx.x*blockDim.x+threadIdx.x;
    if(i<count) out[i]=witness(start+2ULL*i,firstBlock,bits,ps,np);
}
static void checked(hipError_t rc) {
    if(rc!=hipSuccess) { std::fprintf(stderr,"%s\n",hipGetErrorString(rc)); std::exit(1); }
}
int main(int argc,char** argv) {
    if(argc!=3 || (std::strcmp(argv[1],"prefix") && std::strcmp(argv[1],"window")) ||
        (std::strcmp(argv[2],"cpu") && std::strcmp(argv[2],"gpu"))) return 2;
    const auto t0=Clock::now();
    const bool low=!std::strcmp(argv[1],"prefix");
    const u64 end=low?50000000ULL:100000000000000ULL;
    const u64 first=low?4:end-7999998;
    const unsigned count=(end-first)/2+1;
    const u64 b0=first>cap?(first-cap)/30:0, left=30*b0;
    std::vector<u8> bits(end/30-b0+1,255);
    if(left==0) bits[0]&=254;
    unsigned root=std::sqrt((long double)end);
    while(u64(root+1)*(root+1)<=end) ++root;
    while(u64(root)*root>end) --root;
    const unsigned bound=std::max(root,cap);
    std::vector<u8> base(bound+1,1);
    base[0]=base[1]=0;
    std::vector<u16> primes;
    for(unsigned p=2;p<=bound;++p) if(base[p]) {
        if(p<=cap) primes.push_back(p);
        if(u64(p)*p<=bound)
            for(unsigned j=p*p;j<=bound;j+=p) base[j]=0;
        if(p<7 || p>root) continue;
        u64 j=std::max(u64(p)*p,((left+p-1)/p)*p);
        if(!(j&1)) j+=p;
        for(;j<=end;j+=2ULL*p) {
            const int k=wheelbit(j%30);
            if(k>=0) bits[j/30-b0]&=~(1u<<k);
        }
    }
    const auto t1=Clock::now();
    std::vector<u16> out(count);
    if(!std::strcmp(argv[2],"gpu")) {
        u8* b; u16 *ps,*o;
        checked(hipMalloc(&b,bits.size())); checked(hipMalloc(&ps,2*primes.size())); checked(hipMalloc(&o,2ULL*count));
        checked(hipMemcpy(b,bits.data(),bits.size(),hipMemcpyHostToDevice));
        checked(hipMemcpy(ps,primes.data(),2*primes.size(),hipMemcpyHostToDevice));
        hipLaunchKernelGGL(search,dim3((count+255)/256),dim3(256),0,0,first,count,b0,b,ps,unsigned(primes.size()),o);
        checked(hipGetLastError()); checked(hipMemcpy(out.data(),o,2ULL*count,hipMemcpyDeviceToHost));
        checked(hipFree(b)); checked(hipFree(ps)); checked(hipFree(o));
    } else {
        std::vector<std::thread> ts;
        for(unsigned t=0;t<16;++t) ts.emplace_back([&,t] {
            for(unsigned i=u64(count)*t/16;i<u64(count)*(t+1)/16;++i)
                out[i]=witness(first+2ULL*i,b0,bits.data(),primes.data(),primes.size());
        });
        for(auto& t:ts) t.join();
    }
    unsigned bad=0; u16 largest=0; u64 firstAt=0, sum=0, orderHash=0;
    for(unsigned i=0;i<count;++i) {
        const u16 v=out[i];
        bad+=(v==0);
        if(v>largest) {largest=v; firstAt=first+2ULL*i;}
        sum+=v; orderHash=orderHash*0x9e3779b97f4a7c15ULL+v;
    }
    std::printf("%s %s count=%u misses=%u max=%u at=%llu sum=%llu hash=%016llx sieve=%.6f total=%.6f\n",
        argv[1],argv[2],count,bad,(unsigned)largest,(unsigned long long)firstAt,
        (unsigned long long)sum,(unsigned long long)orderHash,std::chrono::duration<double>(t1-t0).count(),std::chrono::duration<double>(Clock::now()-t0).count());
    return bad!=0;
}
```

</details>

<details>
<summary>[P] budget.py</summary>

SHA-256 `8aa146d2985a804d83922a4a92b6e0ab895e9bc8785df1bec422f77ab7597fe9`.

```python
from math import isqrt,ceil
from fractions import Fraction
# Eratosthenes prime-count recurrence over the distinct floor quotients of n.
def pi(n):
    s=isqrt(n)
    q=list(range(1,s+1))
    q+=list(reversed([n//i for i in range(1,s+1) if n//i>s]))
    a={v:v-1 for v in q}
    for p in range(2,s+1):
        if a[p]==a[p-1]: continue
        for v in reversed(q):
            if v<p*p: break
            a[v]-=a[v//p]-a[p-1]
    return a[n]
W=30*2**24
B=4*10**18; C=B//2-1
pc=pi(isqrt(B))
wheel=W//30+(65535+29)//30
print('C, pi, wheel, live, base, cursors, total, partitions',C,pc,wheel,W//16,pc*4,pc*8,wheel+W//16+pc*12,B//W+1)
year=31557600
rows=[('native',24999999,91652351),('wheel CPU',4000000,113785109),('wheel GPU',4000000,114441361),('GPU target',10**9,10**9)]
for label,n,t in rows:
    rate=Fraction(n*10**9,t)
    years=C/rate/year
    print(label,'rate',float(rate),'years',float(years),'nodes2x1yr80%',ceil(2*years/Fraction(4,5)),'time100nodes2x80%',float(2*years/80),'milestones hours',*[round(float(Fraction(b//2-1,1)/rate/3600),6) for b in [10**10,10**12,10**14]])
print('bytes proto source')
```

</details>

