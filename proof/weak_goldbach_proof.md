# Three primes under the generalized Riemann hypothesis

**Theorem.** Assume every nontrivial zero of every primitive Dirichlet
$L$-function, including the Riemann zeta function, has real part $1/2$.
Every odd integer $N\ge10^{22}$ is the sum of three primes.

GRH is a hypothesis throughout. The reported November 2026 Lean certification
attributed to Alpöge has no supplied statement or certificate identifying what
was formalized. No certification claim is needed in the argument.

Put $X=N/2$, $L=\log X$, $Q=\lfloor\sqrt{2\pi X}\rfloor$,
$H=\lfloor X^{3/8}\rfloor$. Write $e(x)=\exp(2\pi ix)$ and
$S(\alpha)=\sum_{n\ge1}\Lambda(n)e^{-n/X}e(n\alpha)$.
All integrals on the circle use Lebesgue measure of total mass one.

## Lemma 1. The primitive-character estimate

For $d\le q\le Q$, a primitive character of conductor $d$, and
$|\beta|\le1/(qQ)$, write $u=2\pi X\beta$, $v=1+|u|$ and
$z=(1-iu)/X$. Let $\delta=\pi/2-|\arg z|$. Then
$\delta\ge1/v$ (integrate or differentiate
$\arctan(1/t)\ge1/(1+t)$), $qv\le Q+2\pi X/Q<5.1\sqrt X$,
and $|z|^{-1/2}\le2^{1/4}\sqrt{X/v}$. We use the estimate
$$
\left|\sum_n\chi(n)\Lambda(n)e^{-nz}-{\mathbf1_{d=1}\over z}\right|
\le 3\sqrt{2\pi}\,|z|^{-1/2}v[\log(10dv)+3]
  + 40\log(10d)+40+|\log z|
  +100|z|^{1/2}v[\log(10dv)+3].                 \tag{1}
$$
The logarithm has its principal value.

**Zero sum.** With multiplicities, let $A(t)$ count ordinates of absolute
value at most $t$, including central zeros. The supplied Bennett–Martin–
O’Bryant–Rechnitzer Corollary 1.2 and Backlund bounds give
$A(t)\le(t+2)\log(10d(t+2))$. Indeed for $d>1,t\ge1$ use the second
error bound, majorizing the main term by $(t/\pi)\log(d(t+2))$.
Below 1 use the same upper estimate at 1, which is less than
$2\log(20d)$ for $d\ge3$. For zeta there are no zeros below 14 and
above 14 the doubled error plus $7/4$ is at most
$1.16\log t+10.45$, absorbed by the displayed majorant after allowing
$(t/\pi)\log t$ for the main term.
By Tonelli, $\sum_\rho e^{-|\gamma|/v}=\int_0^\infty e^{-y}A(vy)dy$.
Use $vy+2\le v(y+2)$ and $\log(y+2)\le y+1$.
The moments of $y+2$ and $(y+2)(y+1)$ against $e^{-y}dy$ are 3 and 7.
The gamma identity on the critical line now bounds
$\sum_\rho|\Gamma(\rho)z^{-\rho}|$ by the first term of (1).

**Shift and residue at zero.** Let $a$ be the parity and $F$ the entire
completion $(d/\pi)^{(s+a)/2}\Gamma((s+a)/2)L(s,\chi)$,
with the extra factor $s(s-1)$ for zeta.
Its Hadamard product gives
$$
 {F'\over F}(s)-{F'\over F}(2)
 =\sum_\rho{2-s\over(s-\rho)(2-\rho)},\qquad
 \sum_\rho\Re{1\over2-\rho}=\Re{F'\over F}(2).
$$
For the second identity take real parts of the first at any nonzero-value
point on the critical line. The functional equation makes the real part
of the logarithmic derivative there zero. At 2 the Euler series gives
$|L'/L|\le\sum_{n\ge2}(\log n)/n^2<2$ (integral comparison).
The completion thus gives $|F'/F(2)|\le\log(10d)+5$.
At zero $|2-\rho|/|\rho|\le3$ by GRH, so the absolute sum of the
differences at zero is at most four times $\Re F'/F(2)$.

Write $L'/L(s)=m/s+b+O(s)$ at zero. Here $m=1$ for even nonprincipal
primitive characters and zero otherwise. Indeed $F(0)\ne0$ by the
Hadamard product over nontrivial zeros, and the completion factors give
these orders (the zeta polynomial cancels the gamma pole).
Solving for $L'/L$ gives $|b|\le 40\log(10d)+38$ by the preceding
bounds: the conductor contributes at most $\frac12|\log(d/\pi)|$,
the gamma constant at most 2 by
$\psi_\Gamma(1)=-\gamma_E$, $\psi_\Gamma(1/2)=-\gamma_E-2\log2$,
and the zeta polynomial constant at most 1. Here $\psi_\Gamma=\Gamma'/\Gamma$.
Thus the residue of $-(L'/L)\Gamma(s)z^{-s}$ at zero is
$-b+m(\gamma_E+\log z)$. The only pole from $L$ itself is the zeta
pole at 1, with residue $1/z$ in the integrand. All other trivial zeros
are at $-a-2j<0$ and lie at or to the left of $-1$.

**Vertical integral.** At $s=-1/2+it$ the functional equation yields
$$
 |L'/L(s)|\le |\log(d/\pi)|+
 \tfrac12\big(|\psi_\Gamma((s+a)/2)|+
 |\psi_\Gamma((1-s+a)/2)|\big)+6
 \le 25+\log(10d)+2\log(2+|t|).
$$
The 6 bounds $\sum_{n\ge2}\log n/n^{3/2}$ by integral comparison
(separate $n=2,3$). For the digammas use the recurrence
$\psi_\Gamma(w)=\psi_\Gamma(w+1)-1/w$ with $|1/w|\le4$.
In the series $-\gamma_E+\sum_{k\ge0}(1/(k+1)-1/(k+w+1))$
split at $K=\lceil2+|t|\rceil$. The first $K$ terms cost at most
$1+\log K+4/3+\log(1+4K/3)$ by integral comparison.
The rest costs at most $|w|\sum_{k\ge K}k^{-2}\le3$.
These give $|\psi_\Gamma(w)|\le 15+2\log(2+|t|)$.
On the shifted line $|\Gamma(s)|\le2\sqrt{2\pi}e^{-\pi|t|/2}$
by the gamma recurrence. Integrating, substituting $|t|=vy$ and using
$\log(2+vy)\le\log v+y+1$, bounds the integral divided by $2\pi$
by the last term of (1).

For clarity, Mellin inversion of the exponential on $\Re s=2$ gives
the original series by absolute convergence. The rectangular shifts
can be taken at positive and negative heights of magnitude in $[T,T+1]$
at distance at least $T^{-2}$ from all ordinates, for all sufficiently
large $T$ (fixed $d$), since the deleted intervals have total length
$O_d(T^{-1}\log T)$. On those segments the Hadamard difference formula
gives polynomial growth: ordinates up to $2T+4$ contribute polynomially
by the distance bound and the count above, and the rest contribute
$O(T\sum_{|\gamma|>2T+4}|\gamma|^{-2})$. The gamma logarithmic derivative
has polynomial growth there by the same series and recurrence.
The exponential decay needed on the horizontal sides follows directly
by rotating the Euler integral for $\Gamma(s+2)$ through an angle of
magnitude $(\pi/2+|\arg z|)/2$ with the sign of $\Im s$, then using
the recurrence twice. The rotation follows by Cauchy's theorem since the
angle is less than $\pi/2$. This gives exponential decay after multiplication
by $z^{-s}$. The residue theorem now proves (1).

## Lemma 2. Arc approximation and major/minor errors

Use the arcs $|\alpha-a/q|\le 1/(2qQ)$ about reduced fractions with
$q\le H$, distances taken modulo one. Distinct centers have distance at
least $1/(qq')$, whereas the sum of radii is $(q+q')/(2qq'Q)<1/(qq')$.
On their union put $M=\mu(q)/(\varphi(q)z)$, taking
$\beta=\alpha-a/q$. Elsewhere put $M=0$.

For any reduced approximation with $q\le Q$, $|\beta|\le1/(qQ)$,
orthogonality on the units gives coefficients
$\chi(a)\tau(\bar\chi)/\varphi(q)$ multiplying the character sums.
If $\chi$ is induced from conductor $d$ and $h=q/d$, insertion of
$\sum_{r\mid(n,h)}\mu(r)$ into the Gauss sum restricts it to units
(the primitive character already vanishes off the units modulo $d$).
In the term $r\mid h$ write $n=rk$. Summing $k$ in lifts of residues
modulo $d$ gives a geometric sum vanishing unless $h/r=1$.
Thus $\tau(\bar\chi)=\mu(h)\bar\chi^*(h)\tau(\bar\chi^*)$.
The primitive Gauss sum has magnitude $\sqrt d$: its additive Fourier
transform off the units vanishes by primitivity (multiplication by a unit
congruent to 1 modulo the reduced additive conductor on which the character
is nontrivial); on units the magnitude is constant, so finite Parseval
gives the result, also for $d=1$. In particular the principal coefficient
is $\mu(q)/\varphi(q)$.

The omitted nonunit terms lie on powers of primes dividing $q$. Passing
from an induced to a primitive sum omits powers of $p\mid q$, $p\nmid d$.
In either case their total absolute weight is at most $3L^2$: for each
prime the terms up to $X$ cost at most $L$, and the subsequent terms cost
at most $\log p\sum_{j\ge0}e^{-2^j}<\log p$. There are at most
$L/\log2$ divisors that are prime, each $p<X$. The total correction is
at most $3(1+\sqrt q)L^2$ after character expansion.

Consequently the pointwise error relative to $\mu(q)/(\varphi(q)z)$
is at most $22 X^{3/4}(L/2+7)$. Here are details of the rounding.
After multiplication by $\sqrt q$ the zero term costs at most
$3\sqrt{2\pi}\,2^{1/4}\sqrt{5.1}X^{3/4}(L/2+7)<21X^{3/4}(L/2+7)$.
For the integral use $|z|\le v/X$, $v\le5.1\sqrt X$ to get
$100\sqrt q |z|^{1/2}v\le1200 X^{1/4}$.
For the residue use $|\log z|\le L+2$, $\sqrt q<2X^{1/4}$.
Together the integral, residue and divisor corrections cost at most
$2000X^{1/4}(L+7)^2<X^{3/4}(L/2+7)$, the latter following at
$X=5\cdot10^{21}$ and thereafter by logarithmic differentiation.

On the complement of the major arcs, Dirichlet approximation gives such a
fraction (pigeonhole the $Q+1$ multiples of $\alpha$ into $Q$ intervals,
then reduce). For $q>H$, the model costs at most $2X^{1-3/16}$,
since $\varphi(q)\ge\sqrt{q/2}$ by multiplying the prime-power factors
$\varphi(p^k)/p^{k/2}$, and $q>X^{3/8}$.
For $q\le H$ one has $|\beta|>1/(2qQ)$ so the cost is at most
$qQ/(\pi\varphi(q))\le\sqrt{2Q}\,Q/\pi<2X^{3/4}$.
We have proved $|S-M|\le XD$ everywhere, where
$$ D=24(L/2+7)X^{-1/4}+2X^{-3/16}. $$

Put $A=1.039(L/2+1)$ and $B=e(1+3L/8)/2$, where here $e=\exp(1)$.
Parseval gives $\int|S|^2\le XA$: use $\Lambda(n)^2\le
\Lambda(n)(L+n/X)$, $(n/X)e^{-2n/X}\le e^{-n/X}$ and partial
summation of the supplied Rosser–Schoenfeld bound $\psi(x)\le1.03883x$.
Also $\int|M|^2\le XB$, by integrating $|z|^{-2}$ over the line
(total $X/2$) and using
$\sum_{q\le H}1/\varphi(q)\le(1+\log H)
\prod_p(1+1/(p(p-1)))\le e(1+\log H)$.
Indeed expand $q/\varphi(q)=\sum_{d\mid q}\mu^2(d)/\varphi(d)$,
and $\sum_{n\ge2}1/[n(n-1)]=1$.

On minor arcs $\int|S|^3\le XD\int_{\mathfrak m}|S|^2$.
On major arcs the cubic difference costs at most $XD$ times the integral
of $|S|^2+|SM|+|M|^2$ there. Adding before applying Cauchy–Schwarz
bounds the total error by $X^2D(A+\sqrt{AB}+B)$.

## Lemma 3. Singular series lower bound and uniform tail

In the Fourier coefficient of $M^3$ the numerator is
$\mu(q)^3 c_q(N)$, with $c_q(N)$ the sum of $e(-aN/q)$ over units.
By the Chinese remainder theorem it is multiplicative in $q$ and
$c_p=p-1$ for $p\mid N$, $-1$ otherwise. For squarefree $q$ this gives
$|c_q|=\varphi((q,N))$. The absolute coefficients are bounded by
$\mu^2(q)/\varphi(q)^2$. Their sum is at most
$\exp(\sum_{n\ge2}1/(n-1)^2)<e^2$ by integral comparison.
Multiplying each by $\sqrt q$ gives product at most
$\exp(\sqrt2+(9/4)\sum_{n\ge3}n^{-3/2})<101$
using $\sum_{n\ge3}n^{-3/2}\le\sqrt2$. Thus the absolute tail
is at most $101/\sqrt H$, uniformly in $N$.

For odd $N$ the factor at 2 equals 2. The other factors are
$1-1/(p-1)^2$ for $p\mid N$ and $1+1/(p-1)^3$ otherwise.
Their product times 2 exceeds $1.32032$. The following reproducible
integer calculation bounds the smaller product from below. The sieve
strikes exactly the composites by their least prime divisor. Each integer
division rounds down. For $m=2000000$, the omitted factors have product
at least $1-\sum_{k\ge m}k^{-2}\ge1-1/(m-1)$ by integral comparison.

```python
from math import isqrt
m = 2_000_000
prime = bytearray([1]) * (m + 1)
for j in range(2, isqrt(m) + 1):
    if prime[j]:
        prime[j*j::j] = bytes((m-j*j)//j + 1)
v = 2 * 10**16
for p in range(3, m+1):
    if prime[p]:
        b = (p-1)**2
        v = v * (b-1) // b
assert v == 13203236743995547
assert v * (m-2) // (m-1) == 13203230142373874
```

## Lemma 4. Main term and singular integral tail

Fourier inversion of $t^2 e^{-t/X}\mathbf1_{t>0}/2$, whose transform
with positive sign is $z^{-3}$ by elementary integration, gives
$\int_{\mathbb R} z^{-3}e(-N\beta)d\beta=2e^{-2}X^2$.
Outside $|\beta|\le w=1/(2qQ)$ the absolute integral is at most
$1/(8\pi^3w^2)$ by integrating $(2\pi|\beta|)^{-3}$.
The total error on extending the integrals divided by $X^2$ is thus
at most $e^2H^2Q^2/(2\pi^3 X^2)\le e^2 X^{-1/4}/\pi^2$.
Extending the series costs at most $2e^{-2}X^2\,101/\sqrt H$.
These estimates apply directly to the coefficient of $M^3$ since the
arc widths depend only on $q$.

## Lemma 5. Prime-power subtraction

The coefficient of $S^3$ counts ordered triples with weight
$e^{-2}\prod_i\Lambda(n_i)$. A coordinate which is a higher prime power
costs at most $1.42620\sqrt N$ in total Mangoldt mass by the supplied
Rosser–Schoenfeld estimate. For a fixed such coordinate the remaining
pair costs at most $1.03883 N\log N$, by summing the first weight
and maximizing the second. Taking the union over three positions
costs less than $13 X^{3/2}(L+1)$, even if the exponential is discarded.

## Lemma 6. Threshold inequality

Combining the preceding lemmas, the strictly prime coefficient divided
by $X^2$ is at least
$$
 2e^{-2}(1.32032-101/\sqrt H)-e^2X^{-1/4}/\pi^2
 -D(A+\sqrt{AB}+B)-13(L+1)X^{-1/2}.
$$
For $L\ge\log(5\cdot10^{21})>49$,
$A+\sqrt{AB}+B\le3\max(A,B)\le1.65(L+3)$.
Each term in $(L+3)D$ decreases: its logarithmic derivative with
respect to $L$ is at most $1/(L+3)+1/(L+14)-1/4$ for the first
summand, and $1/(L+3)-3/16$ for the second.
The other losses also decrease (weakly for the floor).
At the endpoint $L<50$, $X^{1/4}>265000$, $X^{3/16}>11500$,
$H>10^8$. Thus $D<0.00308$, the arc loss is less than $0.270$,
the integral loss is less than $0.000004$, and the prime-power loss
less than $0.000001$. The main term after its series tail exceeds
$0.354$ (use $e^2<7.39$). The resulting positive coefficient proves
the theorem.

## Lemma 7. Prime-ladder reduction

Let $C=4\cdot10^{18}$. Given the finite binary Goldbach verification
through $C$ (Oliveira e Silva, Herzog and Pardi), every odd $7\le n\le C+3$
is covered by the prime 3. More generally an odd prime $p$ covers the
odd integers in $[p+4,p+C]$ by applying the binary result to $n-p$.
Hence any increasing list of odd primes starting at 3, with successive
gaps at most $C-4$ and last prime at least $10^{22}-4$ and at most
$10^{22}$, extends coverage up to the analytic threshold. This is an
implication for a finite ladder; the theorem above does not require a
ladder certificate.

## Constants & inequalities summary

| Quantity | Choice or bound |
|---|---|
| $N_0,X,L$ | $10^{22}, N/2, \log X$ |
| $Q,H$ | $\lfloor\sqrt{2\pi X}\rfloor,\lfloor X^{3/8}\rfloor$ |
| Major half-width | $1/(2qQ)$ |
| $u,v,\delta$ | $2\pi X\beta,1+|u|,\pi/2-|\arg z|$ |
| Dirichlet approximation | $qv<5.1\sqrt X$, $\delta v\ge1$ |
| Primitive explicit formula | Three error terms in (1) |
| Rational approximation error | $22X^{3/4}(L/2+7)$ |
| Uniform model error divided by $X$ | $D=24(L/2+7)X^{-1/4}+2X^{-3/16}$ |
| Squared norms divided by $X$ | $A=1.039(L/2+1)$, $B=e(1+3L/8)/2$ |
| Singular series and absolute tail | $>1.32032$, $\le101/\sqrt H$ |
| Singular integral | $2e^{-2}X^2$ |
| Main term after series tail divided by $X^2$ | $>0.354$ |
| Losses divided by $X^2$ | Arcs $<0.270$, integral truncation $<0.000004$, higher powers $<0.000001$ |
| Finite ladder gap sufficient | $4\cdot10^{18}-4$ |
