# B-007 Wave 3 verification report

[P] Lean **4.16.0**, commit `128a1e6b0a82`, built and independently kernel-replayed **`GoldbachAttack.binaryGoldbachUpTo_50000 : GoldbachAttack.BinaryGoldbachUpTo 50000`**. The exported statement covers all 24,999 even integers from 4 through 50,000. The first five stored ladder primes also have kernel-replayed Pratt proofs. [U] The finite binary premise through 4 × 10¹⁸ and the full Lean ladder remain outstanding. [Issue #6](https://github.com/nisbenz/goldbach-grh-lean/issues/6)

[Q] denotes a source observation, [P] a measured result or demonstrated deduction, [I] an extrapolation or interpretation, and [U] outstanding evidence.

## Native verifier

[Q] The parser requires unsigned decimal digits, checks the end pointer and `errno`, and rejects extra arguments. Both input bounds are capped at 2⁶³−1 to leave room for the sieve, chunk counters, odd round-up and reported endpoints. M must start at 4 or greater. After rounding M up to even, an extension beyond M+3 requires M≥8. The search checks the first rung against M−4, guards unsigned subtraction and checks addition before constructing the next search interval. Binary success requires exactly M/2−1 checked evens. [Source](../../verify/verify_finite.cpp)

[P] Built with `g++ -std=c++17 -O3 -Wall -Wextra -pthread verify/verify_finite.cpp -o /tmp/astra_w3_eng/verify_finite`. Seventeen subprocess regressions completed in 0.027077928 s under a five-second guard.

| M, L | Exit | Result |
|---|---:|---|
| 6, 99 and 4, 99 | 2 | Missing admissible first rung. Zero PASS lines. |
| 2, 99 | 2 | Invalid M. Zero PASS lines. |
| 6, 6 | 0 | Both even integers verified. |
| 8, 27 | 0 | Seven rungs from 3 to 23, maximum step 4. |
| 8, 99 | 2 | Binary phase passes. Ladder stops at 23. |
| 10, 99 | 2 | Ladder stops at 89. |
| 12, 99 | 0 | Both phases pass. |
| 1,000,000, 10,000,000 | 0 | 499,999 evens, then 11 rungs through 10,999,811. |

[P] The requested successful ladder for (8,99) is impossible under the stipulated maximum step M−4. The first required crossing after 23 reaches at least 29, yet 29−23=6>4. Even an exhaustive ladder search cannot reach the required endpoint of 95. The positive (8,27) case exercises the same first rung, and (12,99) exercises the requested endpoint. The suite also rejected M=3, negative input, trailing junk, 2⁶⁴−1 and 2⁶⁴ as M, 2⁶³ as L, and excess arguments. It accepted odd M=7 rounded to 8 with L=11.

## Packed certificate

[P] The generator partitions the range above 3 into 51 pages of at most 1,024 consecutive integer candidates. The first pages end at 15 and 255 to keep every included prime greater than the page's square-root cutoff. Each page stores a product D of at most 1,619 **bits** and proves gcd(D,⌊√high⌋!)=1 in Lean. A balanced tree selects a page and the checker tests n≥2, n≤high and D mod n=0. These facts exclude every possible nontrivial divisor up to √n. Each radix-256 digit supplies one prime summand. The kernel validates both summands and the contiguous coverage from 782 words of 32 digits, including the padding through 50,050.

| [P] Artifact | Source bytes | Object bytes |
|---|---:|---:|
| Unmodified Goldbach/Basic | 965 | 41,392 |
| Shared Blocks | 2,438 | 307,768 |
| Block50000 | 106,519 | 2,164,088 |

[P] Bound-specific build wall time **40.302938188 s**, peak RSS **6,973,848 KiB**. Independent replay wall time **52.203261603 s**, peak RSS **8,415,188 KiB**. Each time includes the launcher and dependency loading. A fresh Mathlib environment replayed every declaration from Goldbach.Basic, Blocks and Block50000, then the kernel checked the named theorem against the separately constructed type. No project-specific axioms or unchecked proof commands occur in those sources. The 100,000 trial had a requested 15-second eligibility threshold. This build exceeded it.

```text
'GoldbachAttack.binaryGoldbachUpTo_50000' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS GoldbachAttack.binaryGoldbachUpTo_50000 : GoldbachAttack.BinaryGoldbachUpTo 50000; replay set 2325 constants
```

[P] Generated source SHA-256 `2f88d495fbd9e67a24f9715b24ca2a841dfd307935419c15d1ba5f86fd1e43a3`. The scratch invocation of the unmodified vendored submission checker returned **REJECTED (not-a-project-module)** during path validation. It accepts PEqualNP or CheckerSuite modules under lean/. The exact-type replay above succeeded independently. [U] A repository submission verdict accepting this module remains outstanding.

## Pratt ladder

[P] The generator read the first five certificates in stored order, tied each root to the corresponding integer in the prime list, and emitted literal modular squaring traces for every distinct recursive factor. Only 2 uses Nat.prime_two directly. Every other prime uses WeakGoldbach.prime_of_lucas_trace from the freshly compiled project source. The five modules share already proved factors. Each root's axiom output was exactly `[propext, Classical.choice, Quot.sound]`. The input JSON SHA-256 was `ef6c41c54bdcdf377b0f387d70a0eae87f211aa8c3ac995f451dcc40c2ceb593`.

| [P] Prefix | Distinct Lucas nodes | Bit steps | Kernel replay + exact root type checks | Seconds per rung | Full replay process | Peak RSS (KiB) |
|---|---:|---:|---:|---:|---:|---:|
| Empty control | 0 | 0 | 0.172526821 s | — | 1.229385340 s | 2,593,856 |
| First rung | 19 | 1,005 | 0.533325118 s | 0.533325118 | 1.629140415 s | 2,598,000 |
| First five | 61 | 4,167 | 1.481904853 s | 0.296380971 | 2.645734543 s | 2,602,392 |

[P] The inner timer encloses Environment.replay and the additional kernel declarations checking each exact Nat.Prime type. Module loading precedes that timer. Pratt.lean built separately in 3.621170940 s. A sequential source rebuild of the five generated modules took 2.783743938, 2.433814800, 2.492874854, 2.343591363 and 2.244497139 s respectively (12.298522094 s total). The five object files total 7,205,096 bytes.

[I] The 2,501-rung JSON contains 13,197 distinct Lucas nodes above 2 and 2,078,098 trace steps after deduplication. Scaling the five-rung replay minus its empty control by the step-count ratio of 498.70 gives **10.9 minutes** for primality replay. Straight per-rung scaling gives **12.4 minutes**. The one-process-per-rung source build projects to **1.71 hours** at the first five's average. Longer imports, larger moduli, sharing, GC and parallel scheduling can change each estimate.

[I] For capacity planning, a separate five-rung process had a 2,598,676 KiB high-water mark after importing the base and peaked at 2,609,180 KiB during the run. A linear model scaling just the 10,504 KiB increase by trace count gives **7.47 GiB** including the base for a single all-rung replay. This is an uncertain estimate from a small increment over startup memory. Historical peaks can hide allocations in existing headroom. A five-rung process measured **2.49 GiB** peak. Holding independently importable batches near that size requires budgeting for shared factor declarations. Scaling the five object files by trace count gives roughly **3.59 GB** on disk.

[Q/U] Replacing certified_prime_ladder_1e22 also requires a single PrimeLadder value with a nonempty list, primality and oddness of every member, ordered steps bounded by B−4 and both endpoint inequalities. Those final proofs and their cost are outside these measurements. The separate binaryGoldbach_4e18 axiom remains even with a complete ladder. [Ladder structure](../../lean/WeakGoldbach/Defs.lean) · [Main theorem](../../lean/WeakGoldbach/Main.lean)

## Reproduction

[P] Save each source block below under its indicated name in /tmp/astra_w3_eng. Run the following from the checkout root with its cached Mathlib and Lean 4.16.0 toolchain. The timing script applies a 57-second kill limit to each Lean invocation. The generated files and their proof obligations are entirely local.

```bash
repo=$PWD
work=/tmp/astra_w3_eng
mkdir -p "$work/Goldbach" "$work/WeakGoldbach"
cp attack/lean/Goldbach/Basic.lean "$work/Goldbach/"
cp lean/WeakGoldbach/Pratt.lean "$work/WeakGoldbach/"
cd "$work"
chmod +x lean-run
python3 timed.py -o Goldbach/Basic.olean Goldbach/Basic.lean
python3 timed.py -o Blocks.olean Blocks.lean
python3 generate.py 50000
python3 timed.py -o Block50000.olean Block50000.lean
python3 timed.py --run Recheck.lean 50000
python3 timed.py -o WeakGoldbach/Pratt.olean WeakGoldbach/Pratt.lean
python3 rungs.py "$repo/verify/ladder_certs.json"
for i in 1 2 3 4 5; do python3 timed.py -o "Rung$i.olean" "Rung$i.lean" || break; done
python3 timed.py --run ReplayRungs.lean
python3 timed.py --run ReplayRungs.lean 3999999999999999887
python3 timed.py --run ReplayRungs.lean 3999999999999999887 7999999999999999883 11999999999999999851 15999999999999999839 19999999999999999817
```

<details>
<summary>[P] lean-run</summary>

```bash
#!/bin/bash
set -eu
cd /tmp/astra_w3_eng
proj=/home/nisbenz/.t3/projects/weak-goldbach/lean
libpath=$(cd "$proj" && lake env printenv LEAN_PATH | tr : '\n' | while read -r path; do realpath -m "$path"; done | paste -sd:)
export LEAN_PATH="$PWD:$libpath"
exec lean +leanprover/lean4:v4.16.0 "$@"
```

</details>

<details>
<summary>[P] timed.py</summary>

```python
import resource, subprocess, sys, time
start = time.perf_counter_ns()
p = subprocess.run(['timeout','-s','KILL','57', './lean-run', *sys.argv[1:]])
print('exit', p.returncode, 'ns', time.perf_counter_ns()-start, 'maxrss_KiB', resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss, flush=True)
sys.exit(p.returncode)
```

</details>

<details>
<summary>[P] generate.py</summary>

```python
from math import isqrt, prod
from pathlib import Path
import sys

bound = int(sys.argv[1])
width = 32
count = (bound // 2 - 1 + width - 1) // width * width
upper = 2 * count + 2
prime = bytearray([1]) * (upper + 1)
prime[:2] = bytes(2)
for p in range(2, isqrt(upper) + 1):
    if prime[p]:
        prime[p*p::p] = bytes((upper - p*p) // p + 1)
primes = [n for n in range(2, upper + 1) if prime[n]]
picks = [next(p for p in primes if p <= n//2 and prime[n-p]) for n in range(4, upper+1, 2)]
base = 1 << max(picks).bit_length()
words = [sum(p * base**j for j, p in enumerate(picks[i:i+width]))
         for i in range(0, count, width)]
source = ['import Blocks', 'namespace GoldbachAttack', 'open Packed',
          'set_option maxRecDepth 100000', 'set_option maxHeartbeats 20000000']
pages = []
low = 3
while low < upper:
    high = min((low + 1)**2 - 1, low + 1024, upper)
    index = len(pages)
    product = prod(p for p in primes if low < p <= high)
    root = isqrt(high)
    source.extend([
        f'private def D{index} : Nat := {hex(product)}',
        f'private theorem cop{index} : Nat.gcd D{index} (Nat.factorial {root}) = 1 := by decide +kernel',
        f'private def page{index} (n : Nat) := decide (2 ≤ n ∧ n ≤ {high} ∧ D{index} % n = 0)',
        f'private theorem page{index}_sound (n : Nat) (h : page{index} n = true) : Nat.Prime n := by',
        '  obtain ⟨lo, hi, rem⟩ := of_decide_eq_true h',
        f'  exact primeOfProduct cop{index} lo ((Nat.sqrt_le_sqrt hi).trans (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr (by decide)))) rem'])
    pages.append((high, f'page{index}'))
    low = high
source.extend(['private def tiny (n : Nat) := decide (n = 2 ∨ n = 3)',
               'private theorem tiny_sound (n : Nat) (h : tiny n = true) : Nat.Prime n := by',
               '  rcases of_decide_eq_true h with rfl | rfl <;> decide'])
def tree(leaves):
    if len(leaves) == 1:
        return leaves[0][1]
    mid = len(leaves) // 2
    cut = leaves[mid-1][0]
    left, right = tree(leaves[:mid]), tree(leaves[mid:])
    name = f'branch{cut}'
    source.extend([f'private def {name} (n : Nat) := if n ≤ {cut} then {left} n else {right} n',
                   f'private theorem {name}_sound (n : Nat) (h : {name} n = true) : Nat.Prime n := by',
                   f'  unfold {name} at h', '  split at h',
                   f'  · exact {left}_sound n h', f'  · exact {right}_sound n h'])
    return name
mark = tree([(3, 'tiny')] + pages)
source.extend([f'private def witnesses : List Nat := [{",".join(map(hex, words))}]',
               f'theorem binaryGoldbachUpTo_{bound} : BinaryGoldbachUpTo {bound} :=',
               f'  certified {bound} {base} {width} witnesses {mark} {mark}_sound (by decide +kernel) (by decide +kernel)',
               f'#print axioms binaryGoldbachUpTo_{bound}', 'end GoldbachAttack'])
Path(f'Block{bound}.lean').write_text('\n'.join(source) + '\n')
```

</details>

<details>
<summary>[P] Blocks.lean</summary>

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
<summary>[P] Recheck.lean</summary>

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
<summary>[P] rungs.py</summary>

```python
import sys, json
from pathlib import Path

data = json.loads(Path(sys.argv[1]).read_text())
seen = {2}
def trace(p, g, exp):
    a, b = 1, g % p
    steps = []
    while exp:
        if exp & 1:
            a = a*b % p
        b = b*b % p
        steps.append(f'({a},{b})')
        exp //= 2
    return '[' + ','.join(steps) + ']', a

def emit(cert):
    p, g = cert['p'], cert['g']
    if p in seen:
        return
    seen.add(p)
    for sub in cert['subcerts'].values():
        emit(sub)
    factors, proofs = [], []
    for key, exponent in cert['factors'].items():
        q = int(key)
        steps, residue = trace(p, g, (p-1)//q)
        assert residue != 1
        body.append(f'private def t{p}_{q} : List (Nat × Nat) := {steps}')
        factors.append(f'({q},{exponent},{residue},t{p}_{q})')
        proofs.append('Nat.prime_two' if q == 2 else f'p{q}')
    steps, residue = trace(p, g, p-1)
    assert residue == 1
    body.extend([f'private def t{p} : List (Nat × Nat) := {steps}',
                 f'theorem p{p} : Nat.Prime {p} := by',
                 f'  apply prime_of_lucas_trace {p} {g} (by decide) t{p} (by decide +kernel) [{",".join(factors)}] (by rfl)',
                 '  · intro f hf',
                 '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf',
                 '    rcases hf with ' + ' | '.join(['rfl'] * len(factors))])
    body.extend('    exact ' + proof for proof in proofs)
    body.extend(['  · intro f hf',
                 '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf',
                 '    rcases hf with ' + ' | '.join(['rfl'] * len(factors)) + ' <;> exact ⟨by decide, by decide +kernel⟩'])
for i in range(1,6):
    root = data['certificates'][i-1]
    assert root['p'] == data['primes'][i-1]
    body = [f'import {"WeakGoldbach.Pratt" if i == 1 else "Rung" + str(i-1)}',
            'open WeakGoldbach','namespace RungCert','set_option maxRecDepth 10000']
    emit(root)
    body.extend([f"#print axioms p{root['p']}", 'end RungCert'])
    Path(f'Rung{i}.lean').write_text('\n'.join(body)+'\n')
```

</details>

<details>
<summary>[P] ReplayRungs.lean</summary>

```lean
import Lean.Replay
import Lean.Util.Path
open Lean

def main (args : List String) : IO Unit := do
  let n := args.length
  initSearchPath (← findSysroot)
  let base ← importModules #[{module := `WeakGoldbach.Pratt}] {}
  let mut cs : Std.HashMap Name ConstantInfo := {}
  for i in [:n] do
    let (data, _) ← readModuleData (← findOLean ("Rung" ++ toString (i+1)).toName)
    for c in data.constants do cs := cs.insert c.name c
  let start ← IO.monoNanosNow
  let env ← Environment.replay cs base
  for a in args do
    let some p := a.toNat? | throw (IO.userError "invalid prime")
    let name := ("RungCert.p" ++ a).toName
    let some (.thmInfo _) := env.find? name | throw (IO.userError "missing theorem")
    let typ := mkApp (mkConst `Nat.Prime) (mkNatLit p)
    if let .error _ := env.addDecl {} (.thmDecl {name := `ExactRung, levelParams := [], type := typ, value := mkConst name}) then
      throw (IO.userError "wrong rung type")
  IO.println s!"PASS {n} rungs, {cs.size} declarations, replay-and-type-check ns {(← IO.monoNanosNow)-start}"
```

</details>

<details>
<summary>[P] weights.py</summary>

```python
import json,sys
j=json.load(open(sys.argv[1]))
seen={2}
steps=0
def visit(c):
    global steps
    p=c['p']
    if p in seen: return
    seen.add(p)
    steps+=(p-1).bit_length()+sum(((p-1)//int(q)).bit_length() for q in c['factors'])
    for child in c['subcerts'].values(): visit(child)
for i,c in enumerate(j['certificates'],1):
    visit(c)
    if i in (1,5,2501): print(i,len(seen)-1,steps)
```

</details>
