# B-003 — Parity obstruction to every sieve level < 1

Agent: `agent-b003`. Lease `4661f464d04948ccba5ce67fe42e42d0` (B-003). Date 2026-11-26.
Workspace `/home/eequaled/goldbach`. Read-only w.r.t. git; scratch `/tmp/opencode/b003/`.

**Honesty scope.** This is a research analysis, **not a proof claim** and **not a resolution of
Goldbach**. Nothing here is recorded as `checked` in the AGENTS.md §0 sense (no Lean kernel
check was run, and none is claimed). Claim tags:

- **[Q]** — quoted or directly read from a source file (with line reference).
- **[P]** — algebra I derived and/or a finite computation I actually ran; proof sketch given.
- **[I]** — my inference/interpretation; not a theorem.
- **[U]** — unverified / conditional (e.g. depends on the RH Liouville estimate that the repo
  itself states but which was not machine-checked here).

---

## 1. [Q] The exact construction, quoted

From `goldbach-grh-lean/proof/strong_goldbach_research.md` §3 (lines 124–136) [Q]:

> **Parity test with the actual Goldbach local factors.** Let $\lambda(n)=(-1)^{\Omega(n)}$, and let $h$ be supported on squarefree integers coprime to $N$, multiplicatively defined there by $h(p)=1/(p-2)$, $h(1)=1$. All these primes are odd. Put
> $$ w(n)=\mathbf1_{(n,N)=1}\prod_{p\mid n,\ p\nmid N}(1+h(p)),\quad K=\frac{\varphi(N)}{N}\prod_{p\nmid N}(1+h(p)/p),\qquad a_n^\pm=K^{-1}w(n)(1\pm\lambda(n)),\quad 1\le n\le N . $$
> These are synthetic, nonnegative weights. The plus sequence has **no primes**. For either sign and squarefree $(d,N)=1$, for fixed $0<\eta<1/4$, under RH one has uniformly
> $$ \sum_{d\mid n,\ n\le N}a_n^\pm =\frac{N}{\varphi(d)}+O_\eta\big(N^\eta(N/d)^{1/2+\eta}\big),\qquad d\le N. \tag{5} $$
> For $(d,N)>1$ the sum is zero. Thus even distribution in the divisor tests to **every fixed level below one**, with a power saving in the sum of errors, does not force a single prime.

From the same file, line 122 [Q]: the prime-density in the divisor test is $g(d)=1/\varphi(d)$, the GRH progression error summed absolutely gives useful level $D=N^{1/2}/\log^B N$, and the dimension-one lower sieve function vanishes for $s=\log D/\log z\le2$; the parity model is not claimed to mimic every statistic of primes (line 148) [Q].

From line 148 [Q]: the error summed over $d\le N^{1-\delta}$ is
$O_\eta(N^{1+\eta-\delta(1/2-\eta)})$; the main term divided by $K$ is
$Y\prod_{p\mid d}(1+h(p))/(1+h(p)/p)=N/\varphi(d)$ with $Y=N/d$.

From line 172 [Q]:

> A test that really distinguishes the signs would, for example, control $\sum_{dk\in\mathcal R}a_{dk}\lambda(d)\lambda(k)$ on a specified factorization range $\mathcal R$, with the same nonnegative factorization weights as its unsigned mass. For $a^+$ the signed sum equals the full mass term by term. Cancellation of any fixed positive fraction would be new information. … For any nonnegative sequence there the prime mass is **exactly** half the rough mass minus half its Liouville-weighted mass. To use this identity one needs strict domination of the signed sum by the rough mass. For the plus model there is equality. Neither the GRH divisor estimate nor (5) supplies strict domination. This test rejects a deduction from those estimates; it does not rule out an independent bilinear theorem for the genuine prime weights.

From `goldbach-grh-lean/proof/strong_goldbach_erh_attack.md` lines 130–137 [Q], the extension to automorphic tests:

> Use $w,K_0,a_n^\pm$ of §3 of the prior report … $a_n^\pm=K_0^{-1}w(n)(1\pm\lambda(n))$ … each distinct $p\mid n$ on the support contributes $1+h(p)$, $h(p)=1/(p-2)$. Fix a tempered cuspidal $\pi$ of $\mathrm{GL}_r/\mathbb Q$ … **Theorem.** Under the stated automorphic RH and temperedness, for every squarefree $d\le N$ coprime to $N$ and every $\eta>0$,
> $$ \Big|\sum_{d\mid n}(a_n^+-a_n^-)A_\pi(n)V(n/N)\Big| \ll_{\pi,V,\eta} N^\eta(N/d)^{1/2+\eta}. \tag{7} $$
> … the sum over $d\le N^{1-\delta}$ of the errors is $O(N^{1-\delta/2+O(\eta)})$. In particular the prime-free plus model and the minus model pass the same smoothed signed-difference tests with a power saving at every such level.

Line 147 [Q] states the scope limit explicitly: this does not assert the model matches genuine shifted primes for arbitrary observables (e.g. $\operatorname{Frob}_{N-n}$ is not multiplicative in $n$). Line 103 [Q] gives the exact detector that any bilinear route must use: on $1<m<N$, $P^-(m)>N^{1/3}$,
$1_{\mathbb P}(m)=(1-\lambda(m))/2$, so prime mass $=(S-Q-B)/2$ and one needs a signed upper bound $B$ strictly below $S-Q$.

### Why the plus sequence has no primes [Q] + [P]

[Q] The doc asserts it (line 130). [P] The reason is an exact algebraic identity, independent of RH: for any prime $q$, $\Omega(q)=1$, hence $\lambda(q)=-1$ and $1+\lambda(q)=0$, so $a_q^+=K^{-1}w(q)\cdot0=0$ for **every** prime $q$ (not merely those coprime to $N$). By complete multiplicativity $\lambda(dk)=\lambda(d)\lambda(k)$, the plus support consists exactly of integers with $\Omega(n)$ even. This was verified computationally in §3 below: 0 primes in the plus support, $\sum_{p\le X}a_p^+=0.0$ exactly; sample $a_3^+=a_7^+=a_{11}^+=a_{97}^+=a_{99991}^+=0.0$.

---

## 2. [P] The divisor-test algebra, worked out

Let $(d,N)=1$, $d$ squarefree, $Y=N/d$, $\sigma=\tfrac12+\eta$. Since
$\mathbf1_{\Omega(n)\ \mathrm{even}}=(1+\lambda(n))/2$ and $\lambda(dm)=\lambda(d)\lambda(m)$,

$$
S_d^\pm:=\sum_{\substack{d\mid n,\ n\le N}}a_n^\pm
 =\tfrac12\Big[\sum_{m\le Y}K^{-1}w(dm)\ \pm\ \lambda(d)\sum_{m\le Y}K^{-1}w(dm)\lambda(m)\Big].
\tag{A}
$$

The source expansion (lines 140–142) [Q] is

$$
 w(dm)=w(d)\sum_{v\mid(m,N)}\mu(v)\sum_{k\mid m,\ (k,Nd)=1}h(k).
\tag{B}
$$

Insert (B) into the unsigned half of (A) and replace $\lfloor Y/(vk)\rfloor$ by $Y/(vk)$:

$$
K^{-1}\sum_{m\le Y}w(dm)\ \approx\
K^{-1}w(d)\Big(\sum_{v\mid N}\tfrac{\mu(v)}{v}\Big)
          \Big(\sum_{k:\,(k,Nd)=1}\tfrac{h(k)}{k}\Big)Y .
$$

Now [P] evaluate the three factors exactly. First $\sum_{v\mid N}\mu(v)/v=\varphi(N)/N$. Second, since $h$ is supported on squarefree integers coprime to $N$,

$$
\sum_{k:\,(k,Nd)=1}\frac{h(k)}{k}
 =\prod_{p\nmid Nd}\Big(1+\frac{h(p)}{p}\Big)
 =\Big[\prod_{p\nmid N}\Big(1+\frac{h(p)}{p}\Big)\Big]\prod_{p\mid d}\Big(1+\frac{h(p)}{p}\Big)^{-1}.
$$

The bracketed product cancels $K$, leaving

$$
\text{main}=Y\,\frac{w(d)}{\prod_{p\mid d}(1+h(p)/p)}
          =Y\prod_{p\mid d}\frac{1+h(p)}{1+h(p)/p}.
$$

With $h(p)=1/(p-2)$ [Q], for odd $p$:

$$
1+h(p)=\frac{p-1}{p-2},\qquad 1+\frac{h(p)}p=\frac{(p-1)^2}{p(p-2)},\qquad
\frac{1+h(p)}{1+h(p)/p}=\frac{p}{p-1}.
\tag{C}
$$

Hence [P]

$$
\text{main}=Y\prod_{p\mid d}\frac p{p-1}=\frac Nd\cdot\frac d{\varphi(d)}=\boxed{\frac N{\varphi(d)}} .
$$

**This is the crux:** identity (C) is why the local factors $h(p)=1/(p-2)$ are chosen — they force the *same* main term $N/\varphi(d)$ for **both** signs. The signed half of (A) contributes only

$$
\lambda(d)K^{-1}\sum_{m\le Y}w(dm)\lambda(m),
$$

bounded under RH by $O_\eta(N^\eta(N/d)^{1/2+\eta})$ using
$\sum_{m\le t}\lambda(m)\ll_\eta t^{1/2+\eta}$ and the floor-error bound $(Y/(vk))^\sigma$ [Q, and conditional: **U** because RH is assumed and not machine-checked here]. For the unsigned half the floor errors give the same shape [Q]. Therefore (5) [Q/U].

### Where $\theta<1$ lets the parity bias hide [P] + [I]

Put $d\asymp N^{\theta}$ with $0<\theta<1$ fixed. Then

$$
\text{main}\asymp\frac{N}{\varphi(d)}\approx N^{1-\theta},\qquad
\text{error}\ll_\eta N^{\eta}N^{(1-\theta)(1/2+\eta)},
$$

so the **relative** error is

$$
\frac{\text{error}}{\text{main}}\ \ll_\eta\
N^{-\big[(1-\theta)(\tfrac12-\eta)-\eta\big]}
\ =\ N^{-\big(\tfrac{1-\theta}{2}-\eta(2-\theta)\big)} .
\tag{D}
$$

The exponent in (D) is positive precisely when
$\eta<\dfrac{1-\theta}{2(2-\theta)}$. For every **fixed** $\theta<1$ one can choose such an $\eta$ (and $\eta<1/4$), so the relative discrepancy between the plus model, the minus model, and the prime model tends to $0$ polynomially. Summing errors over $d\le N^{1-\delta}$ gives $O(N^{1+\eta-\delta(1/2-\eta)})$ [Q], whose exponent is $<1$ under the same condition; the summed main term is $\asymp N\log N$, so the linear tests are dominated by the main term.

**At $\theta=1$ the mechanism fails:** with $d\asymp N$, main $\approx1$ while error $\approx N^{\eta}$, so the RH bound gives no information. Level 1 is exactly where the $N^{1/2+\eta}$ Liouville saving stops beating the shrinking main term $N/d$. [I] This is a *quantitative* barrier to the deduction, not a theorem that GRH cannot imply Goldbach.

---

## 3. [P] Numerical countermodel at $X=10^5$ (real output)

Script: `/tmp/opencode/b003/countermodel.py` (stdlib only). Raw output:
`/tmp/opencode/b003/countermodel_output.txt`. Reproduce with
`cd /tmp/opencode/b003 && python3 countermodel.py`.

Parameters actually used: $X=N=100000=2^5\cdot5^5$, level $\theta=0.6$,
$D=\lfloor X^{\theta}\rfloor=999$, $\eta=0.1$, $\sigma=0.6$, Euler-product cutoff $P=10^6$
(tail $\lesssim1/(P\log P)=7.238\times10^{-8}$). The weights, $K$, $\lambda$, and both test sums are computed from scratch (no hardcoded outputs). Paste of the actual stdout:

```
=== B-003 parity countermodel, computed ===
X=N=100000, theta=0.6, D=floor(X^theta)=999
eta=0.1, sigma=1/2+eta=0.6, K-cutoff P=1000000
N factors=[2, 5], phi(N)=40000
K=0.568042509552   (truncation tail bound ~1/(P log P) = 7.238e-08)

--- (1) primes in support ---
primes p<=X with a_plus[p] > 1e-15 : 0
sum_True a_plus[p]                : 0.0
primes p<=X with a_minus[p] > 1e-15: 9590
sum_True a_minus[p]               : 33774.93360316152
  p=3: w=2.000000, lambda=-1, a_plus=0.0, a_minus=7.041727
  p=7: w=1.200000, lambda=-1, a_plus=0.0, a_minus=4.225036
  p=11: w=1.111111, lambda=-1, a_plus=0.0, a_minus=3.912070
  p=97: w=1.010526, lambda=-1, a_plus=0.0, a_minus=3.557925
  p=99991: w=1.000010, lambda=-1, a_plus=0.0, a_minus=3.520898

--- (2) divisor tests, all squarefree d<=D with (d,N)=1 ---
tests performed:                         337
max relative error plus  (at d= 843): 3.463141e-01
max relative error minus (at d= 903): 3.609210e-01
max |err| / [X^eta (X/d)^sigma] plus:    1.320875e+00
max |err| / [X^eta (X/d)^sigma] minus:   1.343985e+00
sum of abs errors plus:                  1.400697e+04
sum of abs errors minus:                 1.402101e+04
predicted sum bound X^(1+eta-delta(1/2-eta)), delta=0.4: 5.011872e+04
  sum_err_plus / predicted:              2.794757e-01
  sum_err_minus / predicted:             2.797560e-01
sum_d S_d^+ / sum_d S_d^- (should be ~1): 0.991724332885
mean |S_d^+ - S_d^-| / (X/phi(d)):       2.157685e-01
max  |S_d^+ - S_d^-| / (X/phi(d)):       7.054421e-01
prime mass fraction of M^+:              0.000000e+00
prime mass fraction of M^-:              3.368763e-01
  d=   1: S^+=  99743.2010  S^-= 100259.1649  X/phi(d)= 100000.0000  rel_err=-2.568e-03
  d=   3: S^+=  50914.6671  S^-=  49090.7074  X/phi(d)=  50000.0000  rel_err=+1.829e-02
  d=   7: S^+=  16847.7532  S^-=  16484.8321  X/phi(d)=  16666.6667  rel_err=+1.087e-02
  d=  11: S^+=  10111.1558  S^-=   9887.2511  X/phi(d)=  10000.0000  rel_err=+1.112e-02
  d=  33: S^+=   4714.2753  S^-=   5285.4369  X/phi(d)=  5000.0000  rel_err=-5.714e-02
  d= 231: S^+=    982.0528  S^-=    683.4257  X/phi(d)=  833.3333  rel_err=+1.785e-01
  d= 331: S^+=    321.6682  S^-=    285.0198  X/phi(d)=  303.0303  rel_err=+6.151e-02
  d= 997: S^+=    111.0719  S^-=     92.1128  X/phi(d)=  100.4016  rel_err=+1.063e-01

--- (3) bilinear test on d,k <= sqrt(X), squarefree, (dk,N)=1 ---
pairs (d,k):                     11449
unsigned mass U^+ = sum a^+_dk:  30842.779379079
signed   sum B^+ = sum a^+_dk*lam(d)lam(k): 30842.779379079
B^+ / U^+ (exact theory: 1):     1.000000000000000
B^+ - U^+:                       0.000e+00
unsigned mass U^- = sum a^-_dk:  34089.014061515
signed   sum B^- = sum a^-_dk*lam(d)lam(k): -34089.014061515
B^- / U^- (exact theory: -1):    -1.000000000000000
mass M^+ (d=1 test):             99743.201042   X=100000
mass M^- (d=1 test):             100259.164897   X=100000

elapsed seconds: 0.24
```

Reading of the numbers [P]:

1. **No primes in plus support:** 0 primes with $a^+>10^{-15}$; $\sum_{p\le X}a^+_p=0.0$ exactly, while the minus sequence puts 9590 primes in its support with mass 33774.93. Prime mass fraction: plus $0$, minus $0.3369$. This is an enormous observable difference that the divisor tests below do not detect.
2. **Divisor tests pass for both signs:** over 337 squarefree $d\le999$ coprime to $N$, the largest individual error is within a factor $1.32$ of the doc's RH bound $X^\eta(X/d)^{0.6}$ (an implied constant of order 1 is expected); the summed absolute error $14007$ (plus) and $14021$ (minus) are both **below** the doc's predicted sum bound $50119$ (ratio $\approx0.28$). Both sequences sit at $X/\varphi(d)$ to comparable accuracy: $\sum_d S^+_d/\sum_d S^-_d=0.9917$, and the parity difference $|S^+-S^-|/(X/\varphi(d))$ averages $0.216$ — consistent with the theoretical relative exponent (D), which for $\theta=0.6,\eta=0.1$ is only $0.06$ at $X=10^5$ (i.e. $X^{-0.06}\approx0.5$). At larger $X$ this decays; as $\theta\to1$ it stops decaying.
3. **Bilinear obstruction, exactly:** on 11449 $(d,k)$ pairs with $d,k\le\sqrt X$, squarefree and coprime to $N$, the plus signed sum $B^+=30842.779379079$ equals the unsigned mass $U^+=30842.779379079$ with difference $0.000e+00$ and ratio $1.000000000000000$. For the minus model $B^-=-U^-$ exactly. This is the algebraic identity $a^+_{dk}>0\Rightarrow\lambda(dk)=+1\Rightarrow\lambda(d)\lambda(k)=+1$ [P], matching the doc's [Q] statement that "for $a^+$ the signed sum equals the full mass term by term".

**Numerical caveat [U]:** this is a finite check at one $X$; it does not verify RH, does not verify (5) asymptotically, and $K$ is an Euler product truncated at $10^6$. The doc's level-1 claim is conditional on RH and remains [U] in our framework (cf. `audit/REPO_AUDIT.md` C21).

---

## 4. Verdict — can a bilinear test with strict domination beat this?

**Short answer [I]:** not by any estimate that the countermodel itself satisfies. The precise obstruction is the *equality* $B^+=U^+$, not a large error term.

**Detail.** The exact rough-set detector [Q, `erh_attack.md` line 103] says prime mass $=(S-B)/2$ on $P^-(m)>N^{1/3}$. To conclude a **positive** number of representations one must prove, for the genuine sequence, a strict domination $B\le(1-c)S$ with a fixed $c>0$ and a matching lower bound on $S$. But the plus model passes every linear divisor test and every fixed-automorphic signed-difference test of (5)/(7) at level $1-\delta$, while satisfying $B=S$ **identically** (§3, output line 3). Therefore:

1. Any proposed proof of $B\le(1-c)S$ that uses only (5), its summed error, or (7) cannot be valid: those hypotheses are also true of a sequence for which $B=S$. So no such deduction exists. [P + I]
2. Equivalently, the linear tests determine the mass $S$ and its twisted first moments to relative error $o(1)$ for $\theta<1$ (equation D), but $B/S$ takes the value $+1$ on the plus model and would need to be near $-1$ for the genuine prime detector; that sign information lives in a bilinear observable which those tests do not constrain. [I]
3. The obstruction is a **failure of strict domination**, not a contradiction in the bilinear idea. The doc's own qualifier is correct [Q, line 172]: this "does not rule out an independent bilinear theorem for the genuine prime weights". Such a theorem must use a genuinely new input that the synthetic model fails — e.g. off-diagonal information tied to the actual $\Lambda$ coefficients (the missing two-form/dispersion estimate, audit B-011/B-002), not a sharpening of the linear divisor tests. [I]
4. Level $\theta=1$ is the exact boundary in the RH argument (equation D): the Liouville saving $N^{1/2+\eta}$ per divisor ceases to beat the main term $N/\varphi(d)$ when $d\asymp N$. Below level 1 the model is invisible to every linear test; at level 1 the unconditional RH-based estimate itself gives nothing. [P/I]

**No solution is claimed.** B-003 remains an obstruction to a *class of deductions*, not a theorem of independence of Goldbach from GRH/ERH. [I] Consistent with `audit/REPO_AUDIT.md` C19 and its cross-cutting note (lines 344–346).

---

## 5. Claim register

| id | tag | claim |
|---|---|---|
| 1 | [Q] | Weights $a_n^\pm=K^{-1}w(n)(1\pm\lambda(n))$, $h(p)=1/(p-2)$, $K=(\varphi(N)/N)\prod_{p\nmid N}(1+h(p)/p)$; divisor test (5) with error $O_\eta(N^\eta(N/d)^{1/2+\eta})$, level every fixed $<1$ (`research.md` 124–136). |
| 2 | [Q] | Automorphic extension (7) and the statement that plus/minus pass signed-difference tests at every level $1-\delta$ (`erh_attack.md` 130–137). |
| 3 | [Q] | Bilinear strict-domination discussion and exact detector $1_{\mathbb P}=(1-\lambda)/2$ (`research.md` 172; `erh_attack.md` 97–103). |
| 4 | [P] | $\lambda(q)=-1$ for prime $q$, so $a_q^+=0$ for all primes: algebraic, plus finite check (0 primes in plus support, sum $=0.0$). |
| 5 | [P] | Main term evaluation: $K$ cancels, (C) gives $\prod_{p\mid d}p/(p-1)$, hence $N/\varphi(d)$ for both signs. |
| 6 | [P] | Relative-error exponent (D); positive for fixed $\theta<1$ with $\eta<(1-\theta)/(2(2-\theta))$; zero/negative at $\theta=1$. |
| 7 | [P] | Finite check at $X=10^5$, $\theta=0.6$: 337 tests, max individual error ratio 1.32 to the doc bound, summed error $1.4\cdot10^4<5.01\cdot10^4$; $B^+/U^+=1$ and $B^-/U^-=-1$ exactly over 11449 pairs. |
| 8 | [U] | RH (and automorphic RH) estimate (5)/(7) itself — quoted, not machine-checked; repo audit records it as conditional. |
| 9 | [I] | Strict-domination obstruction is a limitation on a deduction from those tests, not logical independence of Goldbach; an independent bilinear theorem for true $\Lambda$ is not excluded. |

## 6. Files, sizes, desk state

- `audit/B003_PARITY_ANALYSIS.md` — this file.
- `agents/CHECKPOINT_B-003.md` — updated checkpoint.
- `/tmp/opencode/b003/countermodel.py` — script, scratch only.
- `/tmp/opencode/b003/countermodel_output.txt` — captured stdout, scratch only.
- Lease taken: `4661f464d04948ccba5ce67fe42e42d0` (B-003), created 2026-11-26T22:37:46Z, expires 23:22:46Z. Released at end with reason `analysis_complete_no_proof`.
- No git operations; no writes to `map/`, `lean/`, `checker/`, `news/`, or the cloned repo.
