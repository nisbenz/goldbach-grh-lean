# The binary Goldbach exceptional set under GRH

**Theorem.** Assume GRH for all primitive Dirichlet characters, including the character of conductor one. For every real $X\ge4$, the number $E(X)$ of even integers in $[4,X]$ which are not sums of two primes satisfies
$$E(X)\le 2\,000\,000\sqrt X(\log X)^3.$$
Consequently $E(X)/(X/2)\to0$. All logarithms are natural.

Use the primitive-character inequality (1) of Lemma 1 and the certified product inequality of Lemma 3 in [the companion proof](weak_goldbach_proof.md). The other numerical inputs are the Rosser–Schoenfeld bounds $\psi(t)\le1.03883t$ and $\psi(t)-\vartheta(t)\le1.42620\sqrt t$ used there, and the finite binary verification of Oliveira e Silva, Herzog and Pardi through $X_0=4\cdot10^{18}$.

## Lemma 1. Arc approximation and squared Fourier error

In a dyadic block take $X\ge X_0$, $L=\log X$, $Q=\lfloor\sqrt{2\pi X}\rfloor$, $H=\lfloor Q/2\rfloor$, $e(t)=\exp(2\pi it)$. Then $L>42$, $2.5\sqrt X\le Q\le2.51\sqrt X$, and $\sqrt X\le H\le1.26\sqrt X$, by the floor bounds. For reduced $a/q$ modulo one with $q\le H$ take half-width $w_q=1/(2qQ)$. Distinct centers have circular distance at least $1/(qq')$, exceeding the sum of their radii since $q+q'\le 2H<2Q$. Put $\beta=\alpha-a/q$ on each arc (using the signed circular displacement), $z=X^{-1}-2\pi i\beta$, and $M(\alpha)=\mu(q)/(\varphi(q)z)$ there. Put $M=0$ elsewhere. Define
$$S(\alpha)=\sum_{m\ge1}\Lambda(m)e^{-m/X}e(m\alpha).$$

We claim $|S-M|\le XD_2$ for $D_2=20X^{-1/4}L$. Here are the details at the present threshold. For any reduced approximation $q\le Q$, $|\beta|\le1/(qQ)$, let $v=1+2\pi X|\beta|$. Then $qv\le Q+2\pi X/Q<5.1\sqrt X$, so $\log(10qv)+3<L/2+7$.
Expansion on the units modulo $q$ gives coefficients $\chi(a)\tau(\bar\chi)/\varphi(q)$, where $\tau(\bar\chi)=\sum_{b\bmod q}\bar\chi(b)e(b/q)$, by finite character orthogonality. Their absolute sum is at most $\sqrt q$ by Cauchy–Schwarz and character Parseval (the sum of squared Gauss sums is $\varphi(q)^2$). The principal coefficient is $\mu(q)/\varphi(q)$ by expanding the unit indicator as $\sum_{r\mid(b,q)}\mu(r)$ and summing the geometric series. Passing to primitive inducing characters and restoring the original nonunits costs at most $3(1+\sqrt q)L^2$. Indeed each omitted prime divides $q$ and its powers through $X$ cost at most $L$, the rest at most $\log p\sum_{j\ge0}e^{-2^j}<\log p$ (use $2^j\ge j+1$). There are at most $L/\log 2$ such primes.

For explicitness the reused primitive inequality, for conductor $d\mid q$, bounds the error from $\mathbf1_{d=1}/z$ by
$$3\sqrt{2\pi}|z|^{-1/2}v[\log(10dv)+3]+40\log(10d)+40+|\log z|+
100|z|^{1/2}v[\log(10dv)+3].$$
After multiplying by $\sqrt q$, the first term is at most $21X^{3/4}(L/2+7)$ because $|z|^{-1/2}\le2^{1/4}\sqrt{X/v}$ and $3\sqrt{2\pi}\,2^{1/4}\sqrt{5.1}<21$. For the last term use $|z|\le v/X$ and $\sqrt{qv}\,v/\sqrt X\le5.1^{3/2}X^{1/4}$. For the middle terms use $X^{-1}\le|z|\le5.1/\sqrt X<1$, $|\log z|\le L+2$, and $\sqrt q<2X^{1/4}$. Including the nonunit corrections, these remaining terms in units of $X^{1/4}$ are at most
$$1200(L/2+7)+2[40(L+3)+40+L+2]+9L^2
\le2000(L+7)^2\le \sqrt X L.$$
For the last inequality $2000(L+7)^2/L\le2800 L$ at $L\ge42$, and $e^{L/2}/L$ increases there with $e^{21}/42>2800$. Thus the rational approximation costs at most $15X^{3/4}L$, since $21(L/2+7)+L\le15L$.

Off the arcs choose such an approximation by placing $Q+1$ multiples $j\alpha$, $0\le j\le Q$, into $Q$ equal bins on the circle, subtracting two in one bin and reducing. For $q>H$ the rational main term is at most $X\sqrt{2/q}\le2X^{3/4}$. Here $\varphi(q)\ge\sqrt{q/2}$ follows by multiplication since $p^{k/2}(1-1/p)\ge1$ for odd $p$ and is at least $1/\sqrt2$ for $p=2$. For $q\le H$ the displacement exceeds $w_q$, so the main term costs at most $qQ/(\pi\varphi(q))\le\sqrt{2Q}Q/\pi<2X^{3/4}$. These estimates prove the claim.

Write $R_2(n),M_2(n)$ for the Fourier coefficients of $S^2,M^2$ with kernel $e(-n\alpha)$. Absolute convergence gives $R_2(n)=e^{-n/X}\sum_{j+k=n}\Lambda(j)\Lambda(k)$, with positive integer indices. Parseval gives
$$\int_0^1|S|^2\le1.039X(L/2+1).$$
Indeed $\Lambda(m)\le L+m/X$, $(m/X)e^{-2m/X}\le e^{-m/X}$, and integration by parts against $\psi$ gives $\sum\Lambda(m)e^{-am/X}\le1.03883X/a$ for $a>0$. Integrating $|z|^{-2}$ over the line gives $X/2$ by the arctangent integral. Hence $\int_0^1|M|^2\le Xe(1+\log H)/2$, where here $e=\exp(1)$. Indeed $q/\varphi(q)=\sum_{d\mid q}\mu^2(d)/\varphi(d)$ by multiplication, so summing $1/\varphi(q)$ to $H$ costs at most $(1+\log H)\prod_p(1+1/[p(p-1)])\le e(1+\log H)$ by the telescoping sum $\sum_{m\ge2}1/[m(m-1)]=1$. Since $\log H\le L/2+\log1.26$, the two squared norms sum to at most $2XL$. Bessel's inequality and $|S+M|^2\le2(|S|^2+|M|^2)$ now give
$$\sum_{n\ge1}|R_2(n)-M_2(n)|^2\le\int_0^1|S^2-M^2|^2
\le 2(XD_2)^2\int_0^1(|S|^2+|M|^2)\le1600X^{5/2}L^3.$$

## Lemma 2. A divisor average for both truncations

Write $I$ for the even integers in $(X/2,X]$, $c_q(n)=\sum_{a\bmod q}^{*}e(-an/q)$ and $a_q(n)=\mu^2(q)c_q(n)/\varphi(q)^2$. By the Chinese remainder theorem the Ramanujan sums multiply in coprime moduli (the unit multipliers in the two additive characters permute the units). At a prime their values are $p-1$ for $p\mid n$ and $-1$ otherwise by geometric summation. For squarefree $q$ their absolute values therefore equal $\varphi((q,n))=\prod_{p\mid q}(1+(p-2)\mathbf1_{p\mid n})$. Expand this product and bound the number of multiples of each divisor $d$ in $I$ by $X/d$, valid even when $d>X$. All terms are nonnegative. This gives
$$\sum_{n\in I}|a_q(n)|\le X b(q)/q^2,\qquad
 b(q)=\mu^2(q)\prod_{p\mid q}\frac{2p}{p-1},$$
since $1+(p-2)/p=2(p-1)/p$.

Put $g(d)=\mu^2(d)\prod_{p\mid d}2/(p-1)$ and let $\tau(m)$ count divisors. Then $b(q)\le\sum_{dm=q}g(d)\tau(m)$, with equality for squarefree $q$ by multiplication. Moreover $\sum_d g(d)/d\le e^2$ by the telescoping sum above and $1+t\le e^t$. For $y\ge1$, counting pairs $ij\le y$ gives $\sum_{m\le y}\tau(m)\le y(1+\log y)$, and summing $1/(ij)$ over those pairs gives $\sum_{m\le y}\tau(m)/m\le(1+\log y)^2$. Thus
$$B(y):=\sum_{q\le y}b(q)\le e^2 y(1+\log y),\qquad
\sum_{q\le y} b(q)/q\le e^2(1+\log y)^2.$$

## Lemma 3. Singular integral and its truncation

The positive-sign Fourier transform of $t e^{-t/X}\mathbf1_{t>0}$ is $z^{-2}$ by elementary integration. Both are integrable, so Fourier inversion gives $J(n)=\int_{\mathbb R}z^{-2}e(-n\beta)d\beta=n e^{-n/X}$. On $I$, $X/(2e)\le J(n)\le X$. Integration on the disjoint arcs gives $M_2(n)=\sum_{q\le H}a_q(n)\int_{-w_q}^{w_q}z^{-2}e(-n\beta)d\beta$. Denote the signed sum of the omitted integrals with these coefficients by $T(n)$. Each omitted integral has magnitude at most $2\int_{w_q}^\infty(2\pi\beta)^{-2}d\beta=qQ/\pi^2$. Hence
$$\sum_{n\in I}|T(n)|\le XQ e^2(1+\log H)^2/\pi^2\le2X^{3/2}L^2,$$
using $2.51e^2/\pi^2<2$ and $1+\log H\le L$.

## Lemma 4. Singular series lower bound and its truncation

For fixed even $n$, the finitely many primes dividing $n$ give local coefficients $1/(p-1)$, and other primes give $-1/(p-1)^2$. The latter are absolutely summable by comparison with $\sum_{k\ge1}k^{-2}$. Thus the product of one plus the absolute coefficients converges, justifying expansion of the signed Euler product. The factor at 2 is 2, and each odd prime factor is at least $1-1/(p-1)^2$. The companion product certificate therefore gives
$$\mathfrak S_2(n)=\sum_{q\ge1}a_q(n)\ge2\prod_{p\ge3}(1-1/(p-1)^2)>1.32032,$$
where the product is over primes. Put $U(n)=\sum_{q>H}|a_q(n)|$. By Lemma 2 and $q^{-2}=\int_q^\infty 2t^{-3}dt$, Tonelli gives
$$\sum_{n\in I}U(n)\le 2X\int_H^\infty B(t)t^{-3}dt
\le 2e^2 X(2+\log H)/H\le15\sqrt X L.$$
Here $H\ge\sqrt X$ and $2+\log H\le L$. This divisor-average argument covers all common divisors, including those larger than $H$.

## Lemma 5. Prime-power subtraction

The contribution to $R_2(n)$ of ordered pairs with at least one higher prime power is at most $2L(\psi(X)-\vartheta(X))\le2.85240\sqrt X L<X/100$. Indeed fixing either coordinate determines the other, whose weight is at most $L$, and the exponential is at most one. The final inequality follows at $X_0$ from $\log X_0<43$ and $\sqrt{X_0}=2\cdot10^9$, then by decrease of $L/\sqrt X$.

## Lemma 6. Dyadic Markov and Chebyshev count

Declare a member of $I$ bad if any of $|R_2-M_2|\ge X/16$, $|T|\ge X/16$, or $U\ge1/16$ holds there. From Lemmas 1, 3 and 4, the three cardinalities are respectively at most
$$409600\sqrt X L^3,\qquad 32\sqrt X L^2,\qquad 240\sqrt X L.$$
Indeed divide the squared-error sum by $(X/16)^2$ and the two first-moment sums by their respective thresholds. On the complement the real coefficient $R_2(n)$ is within $3X/16$ of $J(n)\mathfrak S_2(n)$ by the triangle inequality, since the series error costs at most $J(n)U(n)$. After Lemma 5 the prime-pair weight is strictly positive because $1.32032/(2e)-3/16-1/100>0$. Thus every exception belongs to the union of the three bad sets. Its cardinality is at most $410000\sqrt X L^3$ by $L\ge1$.

## Lemma 7. Global dyadic summation and density

For $4\le X\le X_0$ the finite verification gives $E(X)=0$. Otherwise apply Lemma 6 at $Y_j=X/2^j$ for all nonnegative integers $j$ with $Y_j>X_0$. Their half-open blocks are disjoint and the remaining integers lie at or below $X_0$. Since $\log Y_j\le\log X$, summing the resulting estimates gives
$$E(X)\le \frac{410000}{1-2^{-1/2}}\sqrt X(\log X)^3
\le 2\,000\,000\sqrt X(\log X)^3.$$
Division by $X/2$ gives an upper bound $4\,000\,000L^3e^{-L/2}$ tending to zero (for example $e^{L/2}\ge (L/2)^4/24$).

## Constants and inequalities summary

| Quantity | Value or upper bound |
|---|---|
| Global $(C,c)$ and analytic endpoint | $(2\,000\,000,3)$, $X_0=4\cdot10^{18}$, $42<\log X_0<43$ |
| Denominators and arc radius | $Q=\lfloor\sqrt{2\pi X}\rfloor$, $H=\lfloor Q/2\rfloor$, $w_q=1/(2qQ)$ |
| Floor enclosures | $2.5\le Q/\sqrt X\le2.51$, $1\le H/\sqrt X\le1.26$ |
| Primitive estimate multipliers | $qv<5.1\sqrt X$, zero-term prefactor $<21$, integral prefactor $<1200$ |
| Rational and global errors in units of $X^{3/4}L$ | $15$, $20$ |
| Squared norms divided by $X$ | $1.039(L/2+1)$, $e(1+\log H)/2$, sum $\le2L$ |
| Squared Fourier error | $1600 X^{5/2}L^3$ |
| Divisor-average Euler product | $\sum g(d)/d\le e^2$ |
| Singular integral and series | $X/(2e)\le J\le X$, $\mathfrak S_2>1.32032$ |
| Integral and absolute series tail sums | $2X^{3/2}L^2$, $15\sqrt X L$ |
| Higher-power loss | $2.85240\sqrt X L<X/100$ |
| Bad-set thresholds | $X/16$, $X/16$, $1/16$ |
| Exceptional counts in units of $\sqrt X$ | $409600 L^3$, $32L^2$, $240L$ |
| Surviving prime-weight margin in units of $X$ | $1.32032/(2e)-3/16-1/100>0.045$ |
| Dyadic coefficient and sum factor | $410000$, $(1-2^{-1/2})^{-1}<3.415$ |
