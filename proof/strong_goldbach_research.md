# Pointwise binary Goldbach under Dirichlet GRH

**Outcome.** I find no proof that every even integer is the sum of two primes, even assuming Dirichlet GRH. There is a pointwise conditional reduction down to the endpoint of the finite verification. In the repository's exponential normalization, the complementary arcs to two specified arcs may contribute as little as $-0.764480N$ and positivity still follows. There is also a version for a growing collection of major arcs, and a finite, arithmetic version involving a centered shifted correlation. None of the three signed estimates needed to apply these results is established here.

Throughout, $C=4\cdot10^{18}$, $N\ge C$ is even in the analytic arguments, $X=N$, $L=\log N$, $e(t)=\exp(2\pi it)$, and $e=\exp(1)$ when there is no argument. Use Lebesgue measure of mass one on the circle. The arithmetic input below $C$ is the finite verification of Oliveira e Silva, Herzog and Pardi. The analytic inputs used for explicit constants are the primitive-character inequality (1) of [the weak Goldbach report](weak_goldbach_proof.md), the prime-power bound used in both companion reports, and, only for an alternative reduction in §5, Schoenfeld's classical RH estimate for $\psi$. The two 2026 results are discussed according to their supplied statements.

## 1. An explicit one-sided minor-arc criterion

Set
\[
 S(\alpha)=\sum_{n\ge1}\Lambda(n)e^{-n/N}e(n\alpha),\qquad
 F_N(A)=\Re\int_A S(\alpha)^2e(-N\alpha)\,d\alpha .
\]
For a set invariant under reflection this integral is real even before taking the real part. Absolute convergence and orthogonality give
\[
 F_N(\mathbb T)=e^{-1}\sum_{j=1}^{N-1}\Lambda(j)\Lambda(N-j).
\]
Write $P_N$ for the part of this coefficient with both coordinates prime. The part $B_N$ with at least one higher prime power satisfies
\[
 0\le B_N\le b_N:=e^{-1}2.85240\sqrt N\log N<2.3\cdot10^{-8}N. \tag{1}
\]
Indeed the other coordinate has weight at most $\log N$, either coordinate can be the higher power, and $\psi(N)-\vartheta(N)\le1.42620\sqrt N$. Here and below $L/\sqrt N$ decreases on the range in use and $L(C)<43$. All counts are ordered.

**Theorem 1.** Take $T=17/4$ and let $A$ consist of the two closed arcs of half-width $T/(2\pi N)$ centered at $0,1/2$. Assume Dirichlet GRH and the finite verification. If for every even $N>C$
\[
                         F_N(\mathbb T\setminus A)\ge-0.764480N, \tag{H1}
\]
then every even integer $N\ge4$ is the sum of two primes. On the analytic range the weighted prime-pair coefficient exceeds $2\cdot10^{-6}N$. Only RH for zeta is needed for the major arcs in this theorem. The complement in (H1) includes other small-denominator arcs. A criterion that removes a growing family of rational arcs is given below.

**Proof.** Put $u=2\pi N\beta$ and $Z=N/(1-iu)$. On the first arc the companion primitive inequality with conductor one gives $|S(\beta)-Z|\le300\sqrt N$. In detail, $v=1+|u|\le5.25$. The zero term is bounded by $3\sqrt{2\pi}\,5.25(\log52.5+3)\sqrt N<276\sqrt N$. The other terms together cost at most $40\log10+40+L+2+8500/\sqrt N$, less than $\sqrt N$. The displacement satisfies the lemma's Dirichlet-arc restriction. On the second arc use
\[
 S(1/2+\beta)=-S(\beta)+2\log2\sum_{k\ge1}e^{-2^k/N}e(2^k\beta).
\]
The added term costs at most $2(L+1)$ by splitting at $2^k=N$ and bounding the subsequent exponential sum by $\sum_{j\ge0}e^{-2^j}<1$. Thus $300\sqrt N$ bounds the error relative to $-Z$ there as well. The two model squares have identical kernels since $N$ is even. Their coefficient is $2NJ(T)$, where
\[
 J(T)=\frac1\pi\int_0^T f(u)\,du,\quad
 f(u)=\Re\frac{e^{-iu}}{(1-iu)^2}
 =\frac{(1-u^2)\cos u+2u\sin u}{(1+u^2)^2}.
\]
The total error on these two major arcs divided by $N$ is at most
\[
 d_N=\frac{2T}{\pi}\left(\frac{600}{\sqrt N}+\frac{90000}{N}\right)<8.2\cdot10^{-7}. \tag{2}
\]
This uses their total measure $2T/(\pi N)$ and $|Z|\le N$. The choice of width exploits the phase: $f(u)=\cos(2\arctan u-u)/(1+u^2)$. The end of its first positive lobe is near $4.25023$. The certificate below proves $2J(17/4)>0.764483$ without needing a root approximation. Subtract (1), (2), and the deficit allowed by (H1). The remaining coefficient in units of $N$ exceeds $0.764483-0.000000820-0.000000023-0.764480>0.000002$. Positivity and finite verification prove the assertion.

**Precision and logical strength.** A weaker, variable sufficient hypothesis is the strict inequality
\[
 F_N(\mathbb T\setminus A)>-2NJ(T)+Nd_N+b_N. \tag{3}
\]
It spends exactly the two error allowances proved above. For a particular arc decomposition, the exact boundary is $F_N(\mathbb T\setminus A)>-F_N(A)+B_N$. That last identity is equivalent to Goldbach and provides no independent estimate. Equations (3) and (H1) instead use an independently evaluated major contribution and an explicit upper bound for the nuisance pairs. They require only control of the negative part at one frequency per scale. A two-sided asymptotic, a power saving and control of all frequencies at a single scale are each unnecessary. There is no assertion of optimality among different decompositions.

**Rational certificate for the integral.** The midpoint rule on $k$ equal intervals costs at most $11T^3/(24k^2)$ in the integral, since twice differentiating $e^{-iu}(1-iu)^{-2}$ gives a magnitude bound $1+4+6=11$. Taylor polynomials through degree 26 for both sine and cosine have error at most $r=T^{27}/27!$. Each multiplier in the displayed real formula for $f$ has magnitude at most one. The following certificate uses integer floors and $\pi<355/113$. It can be translated into rational interval arithmetic without any trigonometric evaluations.

```python
from fractions import Fraction as F
from math import factorial
T, k, scale = F(17, 4), 4096, 10**11
total = 0
for j in range(k):
    u = T*(2*j+1)/(2*k)
    h = u*u
    a, b = F(0), F(0)
    for m in range(13, -1, -1):
        a = F((-1)**m, factorial(2*m)) + h*a
    for m in range(12, -1, -1):
        b = F((-1)**m, factorial(2*m+1)) + h*b
    f = ((1-h)*a + 2*h*b)/(1+h)**2
    total += (scale*f)//1
assert total == 115733641602738
lower = T*total/(k*scale) - 2*T*T**27/factorial(27) - 11*T**3/(24*k*k)
assert 2*lower/F(355, 113) > F(764483, 10**6)
```

### A criterion on conventional growing major and minor arcs

Let $y=N/C$, $H=\lfloor2y^{1/16}\rfloor$, $T_y=(17/4)y^{1/16}$. Around every reduced fraction of denominator $q\le H$ take half-width $T_y/(2\pi N)$. Denote the union by $A_y$. Both the denominator cutoff and the rescaled half-width tend to infinity. Put
\[
 D_H(N)=\sum_{q\le H}\frac{\mu^2(q)c_q(N)}{\varphi(q)^2},\quad
 \epsilon=12\sqrt{H/N}(1+T_y)(L+7),\quad
 d_y=\frac{T_y H^2}{\pi}(2\epsilon+\epsilon^2),
\]
where $c_q(N)$ is the sum of $e(-aN/q)$ over reduced residues.

**Theorem 2.** Under the same assumptions, the following single signed estimate for every even $N>C$ implies all-even Goldbach:
\[
 F_N(\mathbb T\setminus A_y)>
              -NJ(T_y)D_H(N)+Nd_y+b_N. \tag{H2}
\]
In particular the uniform hypothesis $F_N(\mathbb T\setminus A_y)\ge-N/3$ suffices. The finite sum in (H2) retains the local arithmetic of the target and requires no pointwise tail estimate for the binary singular series.

**Proof.** The arcs are disjoint since $T_yH^2<\pi N$. For $Q=\lfloor\sqrt{2\pi N}\rfloor$ we have $H\le Q$ and $T_y H Q<2\pi N$, so the primitive estimate applies. On each arc use $M=\mu(q)Z/\varphi(q)$. The character coefficients have absolute sum at most $\sqrt q$ and the nonunit and induction corrections cost at most $3(1+\sqrt q)L^2$, as in Lemma 1 of [the binary exceptional-set report](binary_goldbach_exceptional_proof.md). Here are loose bounds verifying $|S-M|\le N\epsilon$. Write $V=1+T_y\le5.25y^{1/16}$. Then $\log(10qV)+3\le L+7$, $|z|^{-1/2}\le\sqrt N$, $|z|^{1/2}\le\sqrt{V/N}$, and $|\log z|\le L+2$ for $z=(1-iu)/N$. In units of $\sqrt{qN}V(L+7)$ the zero term costs less than 8. The shifted integral costs at most $100\sqrt V/N<1$. The residue costs less than 1 since $40\log(10q)+40+L+2\le 50(L+7)\le\sqrt N(L+7)$. The divisor corrections cost less than 1 since $6L<\sqrt N$. The asserted constant 12 suffices.

Integration of the model square gives exactly $NJ(T_y)D_H(N)$ by summing over the centers. The approximation costs at most $Nd_y$ by $|M|\le N$ and total arc measure at most $T_yH^2/(\pi N)$. This proves (H2) suffices. For the uniform version, $d_y<0.00003$: use $H\le2y^{1/16}$ and $\epsilon\le 63\sqrt{2/C}\,y^{-13/32}(\log C+\log y+7)$. The upper bounds for $\epsilon$ and $y^{3/16}\epsilon$ decrease from $y=1$ by logarithmic differentiation, and $\log C+7<50$.

Fourier inversion of $te^{-t/N}\mathbf1_{t>0}$ gives $J(\infty)=1/e$, so $J(T_y)\ge1/e-1/(\pi T_y)>0.292$. To bound $D_H$ from below, split squarefree $q=db$ into primes dividing $N$ in $d$ and primes coprime to $N$ in $b$. The weight from $d$ is $1/\varphi(d)>0$. In each inner sum $b\le H/d$ the term 1 is present. The total magnitude of all negative terms is at most $\sinh(s)$, where $s=\sum_{p\nmid N}1/(p-1)^2\le\sum_{j\ge1}(2j)^{-2}=\pi^2/24<0.412$. Indeed the degree-$k$ elementary symmetric sum is at most $s^k/k!$, and only odd degrees are negative. Thus every inner sum exceeds $1-\sinh(0.412)>0.575$; retaining $d=1,2$ gives $D_H>1.15$. Now $0.292\cdot1.15-0.00003-0.000000023>1/3$. This proof evaluates the *signed* coefficient on the major arcs. No estimate of the unsigned minor-arc mass occurs in either theorem.
## 2. Attack 1 · The signed minor-arc coefficient and pairs of zeros

The issue is visible at a single frequency. In the companion binary proof's larger Farey dissection, let $E_n=\widehat{S^2-M^2}(n)$. Its GRH estimate is $\sum_{n\ge1}|E_n|^2\le1600N^{5/2}L^3$ at scale $X=N$. Information about the complex coefficients survives in this mean square. Over a block of order $N$ integers it gives root-mean-square size $O(N^{3/4}L^{3/2})$. For a *specified* coefficient its entire allowance is $40N^{5/4}L^{3/2}$. Compared with a fixed positive multiple of $N$ the exponent gap for this deduction is **exactly $1/4$**, plus logarithms. An isolated negative error of size $N$ consumes just $N^2$ of the squared budget. This is a diagnosis of that theorem, not a lower bound on the actual error or on losses in every circle method. Replacing it with the supplied quasi-RH fourth-moment exceptional count still permits an isolated exception. The exceptional-set theorem applies to a different model from (H1); one cannot substitute its average for (H1).

**Keeping the zero phases.** Near zero the zeta explicit formula has oscillatory term
\[
 -\sum_\rho \Gamma(\rho)z^{-\rho},\qquad z=N^{-1}-2\pi i\beta .
\]
On any fixed bounded $\beta$ interval at fixed $N$ this series is absolutely and uniformly convergent by the positive angular distance of $z$ from the imaginary axis, Stirling's bound, and the zero count. Squaring it on an arc and integrating over that arc gives the genuine pair kernel
\[
 K_{w,N}(\rho,\rho')=\Gamma(\rho)\Gamma(\rho')
     \int_{-w}^{w} z^{-\rho-\rho'}e(-N\beta)\,d\beta . \tag{4}
\]
At $a/q$ there are in addition the character coefficients, the factor $e(-aN/q)$, and the residue, principal and cross terms from squaring. GRH sets both real parts in (4) to $1/2$. It supplies neither the sign of (4) nor the cancellation across pairs or centers.

One can quantify what goes wrong in a tempting inversion of (4). For a *finite set* of pairs, replace the integration interval by the line as a separate diagnostic. For $s=\rho+\rho'$ the full-line inverse transform of $z^{-s}$ at positive $N$ is $e^{-1}N^{s-1}/\Gamma(s)$. This follows from the Laplace transform of $t^{s-1}e^{-t/N}/\Gamma(s)$, with symmetric Fourier inversion at $t=N$ (or Abel damping). In particular no absolute-integrability claim at $\Re s=1$ is needed. For zeta zeros with positive ordinates $T\le\gamma,\gamma'\le2T$, Stirling gives
\[
 \left|\frac{\Gamma(1/2+i\gamma)\Gamma(1/2+i\gamma')}
                   {\Gamma(1+i(\gamma+\gamma'))}\right|\asymp T^{-1/2}.
\]
The exponentials in Stirling cancel for the same sign. The Riemann–von Mangoldt formula gives $\asymp T\log T$ ordinates in the block, so the sum of the individual magnitudes of the inverted terms is $\asymp T^{3/2}\log^2T$. They retain the phases of the gamma quotient and of $N^{i(\gamma+\gamma')}$. At $T\asymp N$ this block needs a factor of order $N^{1/2}\log^2N$ to fall to linear scale if treated on its own. The scale is natural since the change in $\gamma\log N$ across one integer is of order $\gamma/N$. This second exponent calculation is for the specific full-line kernel, **not** a proof that one can extend every arc, sum this formula over all zeros or discard higher blocks. In particular the magnitude calculation precludes justifying that interchange by absolute summation. Opposite-sign pairs with comparable magnitudes have exponential damping and do not remove the same-sign difficulty.

Summing the rational centers before estimating gives a twisted Gauss sum $\sum_{a\bmod q}^*\chi(a)\chi'(a)e(-aN/q)$ in the pair term. When $q\mid N$ and $\chi'=\bar\chi$ it equals $\varphi(q)$. Square-root cancellation in **every** such center sum is false. Even at $q=1$ the gamma-quotient phases remain. Equations (3) and (H2) identify exactly how much negative contribution the signed integral may have. I have no GRH bound for that deficit. At no step is the absolute value of the fixed minor coefficient estimated by the unsigned minor-arc second moment.

## 3. Attack 2 · Divisor decompositions and a matched parity countermodel

For the Goldbach sieve take $m=N-p$ with weight $\log p$, omitting $p\mid N$. For squarefree $(d,N)=1$ the divisibility test $d\mid m$ samples primes in the single reduced class $p\equiv N\pmod d$. Its density relative to total mass is $g(d)=1/\varphi(d)$, with zero density if $(d,N)>1$. The individual GRH progression error of order $\sqrt N\log^2(Nd)$ gives, on summing absolute errors to $D$, a useful level $D=N^{1/2}/\log^B N$ for sufficiently large $B$. This computation alone gives no Elliott–Halberstam (EH) level. To leave only primes in $1<m<N$ by trial division one needs a sifting limit just beyond $\sqrt N$. In the dimension-one linear sieve the lower function vanishes for $s=\log D/\log z\le2$. Here $s\approx1$ at the GRH level and is still below 2 at $D=N^{1-\delta},\ z>\sqrt N$. This is only an obstruction for this inference; a decomposition with genuine extra information requires its own test.

**Parity test with the actual Goldbach local factors.** Let $\lambda(n)=(-1)^{\Omega(n)}$, and let $h$ be supported on squarefree integers coprime to $N$, multiplicatively defined there by $h(p)=1/(p-2)$, $h(1)=1$. All these primes are odd. Put
\[
 w(n)=\mathbf1_{(n,N)=1}\prod_{p\mid n,\ p\nmid N}(1+h(p)),\quad
 K=\frac{\varphi(N)}{N}\prod_{p\nmid N}(1+h(p)/p),\qquad
 a_n^\pm=K^{-1}w(n)(1\pm\lambda(n)),\quad 1\le n\le N .
\]
These are synthetic, nonnegative weights. The plus sequence has **no primes**. For either sign and squarefree $(d,N)=1$, for fixed $0<\eta<1/4$, under RH one has uniformly
\[
 \sum_{d\mid n,\ n\le N}a_n^\pm
    =\frac{N}{\varphi(d)}
       +O_\eta\big(N^\eta(N/d)^{1/2+\eta}\big),\qquad d\le N. \tag{5}
\]
For $(d,N)>1$ the sum is zero. Thus even distribution in the divisor tests to **every fixed level below one**, with a power saving in the sum of errors, does not force a single prime.

Here are details of (5). Use the classical RH consequence $\sum_{m\le t}\lambda(m)\ll_\eta t^{1/2+\eta}$ for $t\ge1$. Equivalently, it follows from the usual RH Mertens bound and $\lambda(n)=\sum_{k^2\mid n}\mu(n/k^2)$, since $\sum k^{-1-2\eta}<\infty$. Write $n=dm$, $Y=N/d$, $\sigma=1/2+\eta$. Expand
\[
 w(dm)=w(d)\sum_{v\mid (m,N)}\mu(v)
                \sum_{k\mid m,\ (k,Nd)=1}h(k).
\]
The least common multiple of $v,k$ is $vk$. In the unsigned sum replace $\lfloor Y/(vk)\rfloor$ by $Y/(vk)$ with error at most $(Y/(vk))^\sigma$, including the infinite main-term tail. In the signed sum, complete multiplicativity reduces the inner sum to the same RH estimate at $Y/(vk)$, with zero terms for arguments below one. The errors before division by $K$ are bounded by a constant times
\[
 w(d)Y^\sigma\sum_{v\mid N}v^{-\sigma}
                  \prod_{p\ge3}(1+1/((p-2)p^\sigma)).
\]
The product converges. Each of $w(d),\ \tau(N),\ K^{-1}$ is $O_\delta(N^\delta)$ for every $\delta>0$, by the divisor bound and $N/\varphi(N)\le\tau(N)$. Use $\delta=\eta/3$ for those factors. The main term divided by $K$ is $Y\prod_{p\mid d}(1+h(p))/(1+h(p)/p)=N/\varphi(d)$. Finally, summing (5)'s error for $d\le N^{1-\delta}$ gives $O_\eta(N^{1+\eta-\delta(1/2-\eta)})$; choose $\eta$ sufficiently small for the chosen $\delta$. These are the progression tests on $p=N-n$ used by this sieve, not a claim that the synthetic weights themselves are primes or mimic every statistic of primes.

**Testing other residue classes.** There is a refinement if a proposed sieve also consults *every* residue class for any prescribed finite set of moduli. Let $M$ be their least common multiple, held fixed as $N$ grows, and $W=\operatorname{rad}(M)$. In $w(n)$ omit the factors $1+h(p)$ for $p\mid W$ and insert $\mathbf1_{(N-n,W)=1}$. Normalize by the modified mean
\[
 K_W=\frac{\varphi(N)}N
       \prod_{p\mid W,\ p\nmid N}(1-1/p)
       \prod_{p\nmid NW}(1+h(p)/p).
\]
At $p\mid W$ the local measure on residues modulo any fixed $p^j\mid M$ is uniform on $N-n\not\equiv0\pmod p$, including when $p\mid N$. Thus for $\ell\mid M$ the mass fraction in $n\equiv a\pmod\ell$ is asymptotically $1/\varphi(\ell)$ if $(N-a,\ell)=1$ and zero otherwise. For the divisor test at any $p\mid W,\ p\nmid N$ the surviving class $n=0\pmod p$ still has fraction $1/(p-1)$. Thus (5) retains its main term for every squarefree $d$.

For the error, repeat the expansion proving (5), restricting the final variable $m/(vk)$ to the allowed classes modulo $M$ after substituting $n=dvkt$. Its unsigned count in each class has bounded floor error, or error $\ll_M (Y/(vk))^\sigma$ also for short ranges. For the signed count in a class $b\pmod M$, factor out $(b,M)$ by complete multiplicativity and expand the resulting unit class by characters. The fixed-character GRH bound $\sum_{n\le x}\lambda(n)\chi(n)\ll_{M,\eta}x^{1/2+\eta}$ follows by the same RH Mertens argument with Dirichlet series $L(2s,\chi^2)/L(s,\chi)$ (equivalently use the GRH twisted Mertens bound and the square-divisor convolution). The factors at primes of $M$ and the bounded number of classes only change the error constant. For the unsigned main term these floor densities multiply by CRT, giving exactly the local measures above and the previous local measures away from $W$. This also proves the stated all-class asymptotics by imposing the extra class in the same expansion with $d=1$. The plus sequence still contains no prime. This verifies both tests without assuming uniform control of **all** translated classes of moduli growing with $N$; (5)'s level assertion concerns the divisibility classes actually used in the sieve.

**Bilinear test.** With Dirichlet convolution denoted by $*$, Vaughan's exact identity is
\[
 \Lambda=\mu_{\le U}*\log-\mu_{\le U}*\Lambda_{\le V}*1
              +\Lambda_{\le V}+\mu_{>U}*\Lambda_{>V}*1 .
\]
It follows by inserting $\log=1*\Lambda$ and $\mu*1=\mathbf1_{n=1}$. Paired against $\Lambda(N-m)$, short divisors in the first terms lead to progression estimates or their partial summations. In the last term, after grouping the last two factors, the expression includes
\[
 \sum_{d>U}\mu(d)\sum_{k>V,\ dk<N} b_k\Lambda(N-dk),
 \qquad b_k=\sum_{v\mid k,\ v>V}\Lambda(v).
\]
On the balanced range $d,k\asymp\sqrt N$, treating each progression separately even with a bounded inner weight and length cutoffs would spend $\asymp\sqrt N$ individual GRH error allowances of size $\sqrt N\log^2N$. The actual varying $b_k$ is an additional difficulty. Splitting $k$ again by a Heath-Brown identity introduces a third variable with the same constraint $d k_1 k_2+p=N$. Counting divisor products from their densities in (5), regardless of the number of factors, passes unchanged to the parity model whenever only those linear divisibility tests are used.

A test that really distinguishes the signs would, for example, control $\sum_{dk\in\mathcal R}a_{dk}\lambda(d)\lambda(k)$ on a specified factorization range $\mathcal R$, with the same nonnegative factorization weights as its unsigned mass. For $a^+$ the signed sum equals the full mass term by term. Cancellation of any fixed positive fraction would be new information. More concretely, on integers $1<m\le N$ with all prime factors $>N^{1/3}$, at most two factors are possible. For any nonnegative sequence there the prime mass is **exactly** half the rough mass minus half its Liouville-weighted mass. To use this identity one needs strict domination of the signed sum by the rough mass. For the plus model there is equality. Neither the GRH divisor estimate nor (5) supplies strict domination. This test rejects a deduction from those estimates; it does not rule out an independent bilinear theorem for the genuine prime weights.

In the supplied Li–Liu result, $N=p+rq$ with $r\le q^{a-1}$ implies $r\le N^{(a-1)/a}$. The unconditional and EH exponents for this upper bound are $9/19$ and $2/7$ respectively. A fixed admissible odd prime factor remains possible for arbitrarily large $q$ under either inequality. The conclusion permits two prime factors in the sifted integer and therefore passes this parity test without proving a prime. There is no passage from one fixed $a>1$ to the endpoint $a=1$.

## 4. Attack 3 · Dispersion, zero statistics, and transference

**Dispersion at a fixed target.** For the preceding balanced sum, Cauchy–Schwarz in $d$ and expansion leave off-diagonal products $\Lambda(N-dk_1)\Lambda(N-dk_2)$. Their arguments satisfy $k_2(N-dk_1)-k_1(N-dk_2)=N(k_2-k_1)$. These are two prime weights on linear forms in the same variable. A shifted-divisor or Estermann estimate with divisor coefficients does not estimate this expression with the Mangoldt coefficients. Applying a divisor decomposition to both weights instead creates the signed long-divisor terms of §3. Kloosterman estimates can cancel genuinely oscillatory complete sums; zero frequencies and the coincident index $k_1=k_2$ do not oscillate. Discarding the off-diagonal by an independence assumption is precisely a missing two-form estimate. The matching divisor densities (5) explain why a transfer back from divisor estimates alone is invalid.

**Pair correlation.** The usual Montgomery statistic tests differences $\gamma-\gamma'$ for one zeta family, after averaging with a test function. The full-line same-sign phase of §2 contains $(\gamma+\gamma')\log N$ and a gamma quotient depending separately on both ordinates. Pairs with the same difference can have different values of that phase. Reflecting an ordinate changes a sum into a difference, but it then compares widely separated opposite-sign ordinates with the same non-translation-invariant weight. The rational arcs also involve two possibly different primitive characters and the target-dependent center sum. A standard unweighted or locally scaled pair-correlation conjecture cannot simply be substituted for (4); GRH by itself does not even assert that conjecture. A weighted, conductor-uniform estimate after the sum over centers, valid at **each** even $N$ with the numerical deficit in (H2), would suffice.

**A falsification test for Fourier transference.** In $\mathbb Z/M\mathbb Z$, $M\ge4$ even, reflect by $x\mapsto-x$. From each two-point orbit select one point by an independent fair coin; omit both fixed points. The resulting set $D$ has size $(M-2)/2$ and $(1_D*1_D)(0)=0$ for counting convolution. Yet there is a choice for which every nonzero unnormalized Fourier coefficient is $O(\sqrt{M\log M})$. Indeed each centered contribution is a random sign times $(e(rx/M)-e(-rx/M))/2$, of modulus at most one; the mean at a nonzero frequency has modulus at most one from the omitted points. Hoeffding for the real and imaginary parts and a union bound over $M-1$ frequencies suffice (for example threshold $6\sqrt{M\log M}+1$). Nevertheless the signed sum of the squares of the nonzero Fourier coefficients cancels the **entire** zero-frequency contribution at the missing target, by finite Fourier inversion. The same construction works after thinning each selected point independently; the reflection hole survives. This is a test of density and small individual Fourier coefficients, not a model satisfying Dirichlet GRH. It shows why suppression of individual frequencies, even down to near square-root size, cannot force a binary representation at a fixed reflection center. In the ternary problem the extra Fourier factor provides a different inequality.

## 5. Attack 4 · Centering on the target's reduced residues

One can remove *all* prime divisors of the target before asking for cancellation, without a denominator truncation. Set $\kappa=N/\varphi(N)$, $v(j)=\kappa\mathbf1_{(j,N)=1}$ and $h_j=\Lambda(j)-v(j)$ for $1\le j<N$. Define the signed, finite correlation
\[
 U_N=\sum_{j=1}^{N-1}h_jh_{N-j}.
\]
In the exact exponential framework the coefficient of $(\sum_{1\le j<N} h_j e^{-j/N}e(j\alpha))^2$ at $N$ is $e^{-1}U_N$. Terms with indices at least $N$ never enter. Since $v(N-j)=v(j)$ and there are $\varphi(N)$ units, exact expansion gives
\[
 eF_N(\mathbb T)=U_N+2\kappa\psi_{\rm unit}(N)-\kappa N,\qquad
 \psi_{\rm unit}(N)=\psi(N)-\sum_{p\mid N}\Big\lfloor\frac{\log N}{\log p}\Big\rfloor\log p . \tag{6}
\]
The mixed terms involve just one ordinary prime-counting function. There is no cost from a sum over the characters modulo $N$, even when that modulus is large.

**Theorem 3.** Assuming RH, finite verification and, for every even $N>C$,
\[
                    U_N\ge-(1-1.05\cdot10^{-7})\kappa N, \tag{H3}
\]
every even integer $N\ge4$ is a sum of two primes. A tighter sufficient RHS, with strict inequality, is $\kappa N-2\kappa\psi_{\rm unit}(N)+e b_N$.

**Proof.** Schoenfeld's RH bound $|\psi(x)-x|\le\sqrt x\log^2 x/(8\pi)$ applies for $x\ge73.2$. Each removed prime costs at most $L$, and $\omega(N)\le L/\log2$. Combine (6) and (1). Relative to $\kappa N$, the total losses against the model main term are at most
\[
 \frac{L^2}{4\pi\sqrt N}+\frac{2L^2}{N\log2}
              +\frac{2.85240L}{\kappa\sqrt N}<1.05\cdot10^{-7}.
\]
Use $\kappa\ge2$, $\sqrt C=2\cdot10^9$ and $\log C<43$ at the endpoint. All three upper bounds decrease on the range after replacing $\kappa$ by 2. Hence the prime-pair coefficient is positive.

**Why the hybrid stalls.** On the units, reflection is a permutation. For its even and odd parts $h^{\pm}_j=(h_j\pm h_{N-j})/2$ (also defined on the nonunits), one has the exact difference $U_N=\sum_j(h_j^+)^2-\sum_j(h_j^-)^2$. One-point GRH estimates control the mixed terms in (6); they do not compare these two energies. For a direct test take $N=2^k\ge8$ and select one point from every reflected pair of units. Give selected sites weight $2\kappa$ and all other sites zero. Then the total unit weight is *exactly* $N$, both mixed terms take their model values, and the centered correlation equals $-\kappa N$. There are no fixed units since the two fixed classes are $0,N/2$. This shows that even exact matching of the mixed terms can saturate the negative boundary. It tests the centering inference, not primality. As a sieve test, the even-$\Omega$ model of §3 also matches the local divisor data but has no prime support; its composite mass cannot be subtracted by the prime-*power* estimate (1), which specifically uses $\Lambda$. No primality conclusion for either synthetic sequence is used. Equation (6) isolates the residual without estimating it. Applied at its exact boundary with exact nuisance mass it would merely restate the representation problem.

## Conclusion

The explicit estimates above cover the entire range up to the signed inequalities: there is no gap between the finite and analytic endpoints. The independently certified parts are the major coefficients in Theorems 1–2, the prime-power subtraction and the linear terms in Theorem 3. The unproved inputs (H1), (H2), and (H3) are alternatives. Each requires excluding a large **negative correlation for a specified even target**. Neither the supplied exceptional-set estimates, the tested zero-pair expansion, the divisor-distribution estimates, nor the centering identity excludes it. The calculations supply conditional theorems and obstruction tests, not a proof of Strong Goldbach or a proof that GRH cannot imply it.
