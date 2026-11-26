# Binary Goldbach under ERH and automorphic RH

**November 2026.** I obtain no proof that every even \(N\ge4\) is a sum of two primes under the hypotheses in the question. The sharpest obstruction in the proposed 2026 argument is an exact support calculation. The auxiliary weight in Lü–Wang–Wu vanishes on *every* complement on which their proposed application would need to detect a prime. There are two other difficulties even if one grants cancellation of the unrestricted reflected sum. Its error scale is too large, and the usual lower sieve gives zero at the proposed cutoff.

There are positive results. Section 2 gives a pointwise \(O_\epsilon(N^{3/4+\epsilon})\) error for a specified smooth reflected \(d_2,d_2\) sum and explains what supplies the saving. Section 4 extends the repository's parity model to fixed automorphic coefficient tests at every fixed divisor level below one. It also gives two one-sided reductions. The first has an explicit threshold from the lower linear sieve at \(z=N^{2/9}\); the second uses a positive supply of candidates from Chen's theorem. None uses H1–H3 as an assumption. The explicit criteria H1–H3 and the verification through \(C=4\cdot10^{18}\) are in the [prior report](strong_goldbach_research.md).

Throughout, primes in a representation are ordered when counted, \(L=\log N\), and asymptotic assertions concern sufficiently large even \(N\). I grant the usual analytic continuation and functional equations where they are needed, the stated RH hypotheses, the accompanying temperedness assumptions, and fixed-degree Lindelöf estimates in their usual conductor aspect. Finite-place Ramanujan and the archimedean spectral gap are additional assertions about local parameters. The classical Weil bound for Kloosterman sums is already a theorem. Keeping the origins of these inputs straight matters when summing over a family of moduli or spectral parameters.

## 1. What an extra Frobenius condition measures

Let \(K/\mathbb Q\) be finite Galois with group \(G\), and let \(f\) be a fixed class function. Write \(f=\sum_\rho c_\rho\chi_\rho\) in irreducible characters. Away from ramification, effective Chebotarev estimates
\[
       \sum_{p\le X}(\log p) f(\operatorname{Frob}_p)
           =c_{\mathbf1}X+O_{K,f}(\sqrt X\log^2(2X)).
\]
For example, this can distinguish primes represented by a specified primitive positive definite quadratic form, with the usual splitting and ramification qualifications, by passing to a ring class field. A Kummer condition can distinguish power residues. These are genuine refinements of information on the **one prime** being counted.

The following calculation keeps track of the level when such a restriction is added to the Goldbach sieve. For \((d,N)=1\), insert the character expansion of \(1_{p\equiv N\bmod d}\). For each term the explicit formula now involves \(\rho\otimes\chi\). With Artin holomorphy for the nontrivial irreducibles and ERH, the resulting estimate is
\[
 \sum_{\substack{p\le N,\ p\equiv N\bmod d\\p\ {\rm unramified\ in}\ K}}
  (\log p) f(\operatorname{Frob}_p)
  =N\delta_{K,f}(d,N)+O_{K,f}(\sqrt N\log^2(2Nd)).
 \tag{1}
\]
Here \(\delta\) is the average of \(f(g|_K)1_{g|_{\mathbb Q(\zeta_d)}=N\bmod d}\) in the Galois group of the compositum. This accounts for intersections of fields and incompatible conditions. Indeed, the main coefficients in the character expansion are the multiplicities of the trivial representation. For fixed \(K\), the conductor of a twist is bounded by a fixed constant times \(d^{\dim\rho}\). The character average has total absolute coefficient one before multiplying by the \(c_\rho\). Removing imprimitive Euler factors, ramified primes and higher prime powers fits within the displayed error. This proof also explains why a bare \(O(\sqrt X\log(\Delta X))\) with an absolute constant for arbitrary growing fields, class functions and weight conventions would be unsafe.

Summing the individual error allowances in (1) costs \(O_{K,f}(D\sqrt N\log^2(2ND))\) through \(d\le D\). This supplies every fixed exponent below \(1/2\), also with the extra Frobenius restriction. It gives no larger exponent by this summation. A compositum can impose many conditions on \(p\) at once. In the cyclotomic case, excluding every possible small prime divisor of \(N-p\) amounts to excluding one residue at each such prime. The product modulus for all primes through \(\sqrt N\) already has logarithm \((1+o(1))\sqrt N\). One must estimate a union of classes and account for its character coefficients. Treating it as one fixed-field application of (1) loses both pieces of information.

There is a direct way to see what a successful field argument would still have to do. For nonnegative \(f\) the relevant target in the interior is
\[
  \sum_{p<N}(\log p)f(\operatorname{Frob}_p)\Lambda(N-p).
\]
Equation (1) evaluates this with the last factor replaced by a short divisor expansion. Keeping the last factor requires joint information on the reflected integer. Even a description of both primes by norm forms requires a count of simultaneous norm conditions with the specified sum and prime values. Chebotarev in the compositum imposes simultaneous splitting conditions on a *single* prime. It supplies no such two-input count. This diagnoses the proposed use of ERH and does not establish a logical nonimplication from ERH.

## 2. A spectral calculation that works, and the balanced sum that remains

### A numerical benchmark for genuine divisor coefficients

Here is one precise level and power saving. Write \(d_2=1*1\), and fix \(W\in C_c^\infty((0,1))\). For \(H\in C_c^\infty((0,\infty))\) with fixed compact support, let \(c_q(a)\) be the Ramanujan sum and \(\gamma\) Euler's constant. Define
\[
 M_d(a;H)=\frac1d\sum_{q\mid d}\frac{c_q(a)}q
    \int_0^\infty H(t/N)(\log t+2\gamma-2\log q)\,dt .
\]
Uniformly for \(d\le N\) and any \(a\),
\[
 \sum_{m\equiv a\bmod d}d_2(m)H(m/N)
       =M_d(a;H)+O_{\epsilon,H}(N^\epsilon d^{1/2}).                \tag{2}
\]
All sums over \(m\) here use positive integers. Bounded families with common compact support away from zero and bounded smooth seminorms have uniform constants. Thus the sum of the absolute remainders is \(O_\epsilon(N^\epsilon D^{3/2})\), giving level \(2/3-\delta\) for each fixed \(\delta>0\) relative to scale \(N\).

**Derivation.** Resolve the congruence into additive characters of exact modulus \(q\mid d\). Apply the ordinary divisor Voronoi formula to each reduced additive twist. Its integral term gives \(M_d\). On the dual side the reduced numerator sum is a Kloosterman sum \(S(-a,\pm n;q)\), up to sign conventions. Its absolute value is at most \(\tau(q)q^{1/2}(n,q)^{1/2}\). The two Bessel transforms have size \(O_H(N(1+|\log u|))\) for \(u=nN/q^2\le1\) and \(O_{A,H}(Nu^{-A})\) for \(u\ge1\). These follow from the order-zero Bessel kernels at zero and integration by parts on the smooth support at infinity. For \(Y\ge1\),
\[
  \sum_{n\le Y}d_2(n)(n,q)^{1/2}
     \ll_\epsilon Y^{1+\epsilon}\sum_{g\mid q}g^{-1/2}
     \ll_\epsilon Y^{1+\epsilon}q^\epsilon .
\]
Group the dual variables about \(Y=q^2/N\) in dyadic intervals. For \(Y<1\) all terms have rapid decay and their weighted total after division by \(N\) is \(O_\epsilon(N^\epsilon Y)\). For \(Y\ge1\) the same bound follows from the last display and the logarithmic small-argument bound, absorbing logarithms by adjusting \(\epsilon\). Including the Voronoi factor \(1/q\), the Kloosterman bound and the initial \(1/d\), the total is
\[
 \ll_\epsilon \frac{N^{1+\epsilon}}{d}
       \sum_{q\mid d} q^{-1/2}(q^2/N)
 \ll_\epsilon N^{2\epsilon} d^{1/2}.
\]
Renaming \(\epsilon\) proves (2).

For the **reflected** sum choose a smooth \(v\) on \((0,\infty)\) with \(v(u)+v(1/u)=1\), equal to one on \(u\le1/2\) and zero on \(u\ge2\). Pairing complementary divisors gives \(d_2(n)=2\sum_{d\mid n}v(d/\sqrt n)\), including perfect squares. Put \(H_d(x)=W(x)v(d/\sqrt{N(1-x)})\) on the support of \(W\), and zero elsewhere. This family satisfies the uniformity conditions in (2). Substituting \(n=N-m\) gives the pointwise formula
\[
 \sum_{m=1}^{N-1}W(m/N)d_2(m)d_2(N-m)
       =2\sum_{d\le2\sqrt N}M_d(N;H_d)+O_{\epsilon,W}(N^{3/4+\epsilon}).
 \tag{3}
\]
The finite main term uses only integrals and Ramanujan sums. The exponent is what this argument proves, with no optimality claim. Both (2) and (3) already hold unconditionally. This example identifies the source of the gain precisely. Voronoi turns the whole coefficient sequence into a dual sum of length about \(q^2/N\). Weil then saves in the reduced numerator. The square root of the modulus alone would have given no such conclusion without the dual-length calculation.

### Replacing \(d_2\) by primes

For a smooth Type I sum with one free variable, the prime progression term for each \((d,N)=1\) has main term \(\varphi(d)^{-1}\int H_d(t/N)\,dt\) and error \(O(\sqrt N L^2)\) for \(d\le N\), by Dirichlet GRH and partial summation with uniform bounded variation. Summing with coefficients of size \(O_\epsilon(N^\epsilon)\) up to \(D=N^\alpha\) gives \(O_\epsilon(N^{1/2+\alpha+\epsilon})\). The saving relative to \(N\) is \(1/2-\alpha-\epsilon\). At \(D\asymp\sqrt N\) the power saving disappears, even with the other variable free. The logarithmic-derivative coefficients \(\Lambda\) have an explicit formula involving zeros. They do not have the \(d_2\) dual formula used in (2).

For a balanced box \(d\in I,\ k\in J\) of lengths comparable to \(\sqrt N\), take \(dk<N\) throughout and \((d,N)=1\). Let
\[
 F_d(k)=\Lambda(N-dk)-d/\varphi(d),\qquad
 T=\sum_{k\in J} b_k\sum_{d\in I,\ (d,N)=1}\mu(d)F_d(k).
\]
The subtracted quantity is the progression main density *per* \(k\) of the unrestricted \(k\)-sum. For varying \(b_k\), this only splits off a computable term and asserts no asymptotic. Terms with \(d\) sharing a prime with \(N\) require separate accounting in the original sum. The coprime subproblem already contains the following difficulty. Cauchy–Schwarz in \(k\) gives exactly the quadratic form
\[
 |T|^2\le \|b\|_2^2
 \sum_{d,e\in I}^{*}\mu(d)\mu(e)\sum_{k\in J}F_d(k)F_e(k),       \tag{4}
\]
where the star enforces coprimality to \(N\) in both variables. For the Vaughan coefficient \(|b_k|\ll L\), \(\|b\|_2^2\ll\sqrt N L^2\). The diagonal inside the quadratic form costs \(O(N L^2)\). A sufficient estimate for \(T=o(N)\) is an upper bound \(o(N^{3/2}/L^2)\) on the signed off-diagonal. The termwise absolute allowance there is \(O(N^{3/2} L^2)\). More logarithms must be budgeted if many boxes are added. These are the scales in this specific Cauchy step, not lower bounds on the actual error.

The off-diagonal contains \(\Lambda(N-dk)\Lambda(N-ek)\) along two affine forms in \(k\). Even their expected joint density can differ from the product of the two single densities. A Rankin–Selberg Dirichlet series pairs multiplicative data at a common index. Lindelöf bounds an individual \(L\)-value in terms of its conductor. Neither operation evaluates (4). In a Kuznetsov, Jutila or delta-method approach one would need to transform the **actual** coefficients, keep the resulting lengths, and sum the spectral coefficients, with their signs and dependence on \(N,d,e\). Temperedness bounds individual local parameters. The Weil estimate includes a gcd factor and bounds one complete Kloosterman sum. Neither gives square-root cancellation when adding different spectral terms or moduli. A formal delta-symbol insertion without estimates for the transformed prime or truncated Möbius coefficients leaves (4) unpaid.

There is accordingly no single level or error exponent specified by “Grand RH for all \(\mathrm{GL}_n\)” for the whole collection of \(d_k,d_\ell\), all sharp or smooth cutoffs, or all Type I/II/III weights. Even where a degree-\(k\) Voronoi formula is available, its conductor and dual length differ from those of degree two. A fixed smooth divisor convolution, the product of two truncated sieve coefficients, and a reflected prime convolution pose distinct estimates. Equations (2)–(4) give actual exponents for specified problems and a quantitative target for the unresolved one. No saving for the balanced Goldbach box follows here by substituting \(k,\ell\) in (3).

## 3. The 2026 Möbius mechanism at the Goldbach cutoff

In the cached Lü–Wang–Wu manuscript, Theorem 1 asserts \(\sum_{p\le x}\mu(p+2)=o(\pi(x))\). Remark 3 says one may generalize the shift in \(\mu(p+h_1)\) to \(h_1\asymp x\) under quasi-RH and leaves details to the reader. In particular it gives no written proof of the reflected, target-uniform assertion for \(\mu(N-p)\). A positive large shift and a reflection also have different endpoints. Grant even the reflected assertion for this test.

**Exact prime detector.** Take \(z=N^{1/3}\), write \(m=N-p\), and restrict to \(1<m<N,\ P^-(m)>z\). Such an \(m\) is a prime, a product of two distinct primes, or a prime square. Consequently
\[
   1_{\mathbb P}(m)=\frac{\mu^2(m)-\mu(m)}2
                    =\frac{1-\lambda(m)}2,\qquad
   \lambda(m)=(-1)^{\Omega(m)}.                                  \tag{5}
\]
The suggested \((1-\mu(m))/2\) incorrectly gives half weight to each prime square. The number of these squares is at most \(\sqrt N\) before imposing primality on \(p\). If \(S\) counts the rough complements, \(Q\) the squares, and \(B\) the sum of \(\mu(m)\) on this set, the exact count of representations *on this set* is \((S-Q-B)/2\). In particular a quantitative application needs a positive lower bound for \(S-Q\) and a signed upper bound for \(B\) strictly below it. Cancellation alone with an unspecified or possibly zero denominator does not suffice.

**Support of the weight.** In equations (2.12)–(2.13) of the manuscript, \(L_x=\log x\),
\[
 \mathcal P_i=(\exp(L_x^{a_i}),\exp(2L_x^{a_i})]\cap\mathbb P,
 \quad 1/10<a_1<\cdots<a_K<1/5,\qquad
 W(m)=\prod_{i=1}^K\frac{\rho^{\omega_i(m)-1}\omega_i(m)}{V_i},
\]
where \(\omega_i(m)=\#\{r\in\mathcal P_i:r\mid m\}\), \(V_i=\sum_{r\in\mathcal P_i}1/r\), and \(0<\rho<1\). The intervals are disjoint for sufficiently large \(x\). Each nonzero term supplies \(K\) distinct prime divisors and hence a factorization \(m=ah\), \(a=r_1\cdots r_K\), before Cauchy–Schwarz in the cofactor and dispersion. The manuscript also uses \(U=V=x^{1/5}\) and a separate sifted weight on the variables in Vaughan's identity. Sifting the input of Vaughan's identity is different from sifting its shifted output.

For \(x\asymp N\), all the \(\mathcal P_i\) lie below \(N^\theta\) for every fixed \(\theta>0\) once \(N\) is large. Thus
\[
  1_{P^-(m)>N^\theta}W(m)=0\qquad(K\ge1).                       \tag{6}
\]
The same holds for every one of the finitely many families \(W_j\) used to remove the weight in §5.3. On the rough set the difference between 1 and *any* linear combination of those weights is exactly 1. An approximation small in an unrestricted average can lose the entire restricted average. At the expected Goldbach scale \(N/L^2\) in unweighted units, even an unrestricted error \(o(N/L)\) is insufficient. Equivalently, an error of order \(N/L^2\) on the rough set can be canceled, or simply absorbed, in the statement of the unrestricted theorem.

**Changing the cutoff or the extracted primes.**

* At \(z=N^{1/3}\), a linear sieve of level \(N^\alpha\) has \(s=3\alpha\). Its dimension-one lower function vanishes for \(s\le2\). The direct GRH level gives \(s\) near \(3/2\). A level strictly exceeding \(2/3\) would make the usual rough *unsigned* lower estimate available; (6) would still annihilate the proposed signed estimate. The \(2/3\) in (2) concerns a different sequence.
* For \(\theta<1/4\) one may choose \(2\theta<\alpha<1/2\) and get a positive unsigned lower sieve. For \(1/5<\theta<1/4\), \(\Omega(m)\le4\) on the rough set. The negative Liouville sign then counts primes **and** three-prime products with multiplicity. Both issues are concrete: (6) still holds, and a proof must bound the three-factor contribution or give it a nonpositive weight. At a subpower cutoff that admits the original \(\mathcal P_i\), the bound \(\Omega(m)\le\log N/\log z\) no longer excludes any fixed number of factors.
* Moving the \(K\) intervals *above* the cube root permits no terms if \(K\ge3\). For \(K=2\) every surviving term is a semiprime. For \(K=1\) the prime contribution has \(h=1,\ a=m\), and occurs only if the extracted interval contains that prime. On this slice, estimating the prime contribution is precisely counting \(p+a=N\) with \(a\) prime in the selected interval. Dispersion over a long cofactor has disappeared. Dropping the weight altogether removes the factorization used in its proof.
* Li–Liu's supplied \(1+1.9\) theorem gives \(m=rq\), \(r=1\) or \(r\le q^{0.9}\) prime. A composite witness has \(r\le N^{9/19}\); in the EH version the exponent is \(2/7\). These follow from \(r\le(m/r)^{a-1}\). They limit the *upper* size of the smaller factor. They neither force \(r=1\) nor supply a lower bound for \(r\) on the cube-root rough set. In the EH version all composite witnesses even have \(r<N^{1/3}\). EH is an additional distribution hypothesis. Passing to a weighted sieve can isolate a more favorable set of semiprimes, but a parity estimate for that set is still needed.

## 4. What survives the stronger tests

### A conditional theorem on automorphic tests of the parity model

Use \(w,K_0,a_n^\pm\) of §3 of the prior report, writing \(K_0\) for its normalizing constant. Thus \(a_n^\pm=K_0^{-1}w(n)(1\pm\lambda(n))\), \(w\) vanishes on \((n,N)>1\), and each distinct \(p\mid n\) on the support contributes \(1+h(p)\), \(h(p)=1/(p-2)\). Fix a tempered cuspidal \(\pi\) of \(\mathrm{GL}_r/\mathbb Q\) and let \(A_\pi(n)\) be the normalized Dirichlet coefficients of its standard \(L\)-function. Fix \(V\in C_c^\infty((0,1))\).

**Theorem.** Under the stated automorphic RH and temperedness, for every squarefree \(d\le N\) coprime to \(N\) and every \(\eta>0\),
\[
 \left|\sum_{d\mid n}(a_n^+-a_n^-)A_\pi(n)V(n/N)\right|
 \ll_{\pi,V,\eta} N^\eta(N/d)^{1/2+\eta}.                       \tag{7}
\]
The weights are extended by zero outside \([1,N]\). For a fixed cuspidal \(\pi\) of degree at least two, the same bound holds for either sign individually. For each fixed \(\delta>0\), the sum over \(d\le N^{1-\delta}\) of the errors is \(O(N^{1-\delta/2+O(\eta)})\). In particular the prime-free plus model and the minus model pass the same smoothed signed-difference tests with a power saving at every such level. The theorem allows any prescribed finite list of representations.

**Proof.** Put \(Y=N/d\), \(n=dm\), and extract \(2\lambda(d)w(d)/K_0\) in the difference. The Dirichlet series of the remaining coefficient of \(V(m/Y)\) is \(L(s,\pi)^{-1}H(s)\). To see the factorization, put \(t=p^{-s}\). At \(p\nmid Nd\) the original factor is
\[
 1+(1+h(p))\sum_{j\ge1}(-1)^j A_\pi(p^j)t^j .
\]
Multiplying by \(L_p(s,\pi)\) leaves \(1+O_{r,\eta}(h(p)|t|+|t|^2)\) on \(\Re s\ge1/2+\eta\). Temperedness gives \(|A_\pi(p^j)|\le {j+r-1\choose r-1}\). The good factors therefore converge absolutely there. At \(p\mid N\) the original factor is 1. At \(p\mid d\) it is \(\sum_{j\ge0}(-1)^j A_\pi(p^{j+1})t^j\), since \(d\) is squarefree. This expression also handles \(A_\pi(p)=0\). Each exceptional factor after multiplication is bounded by a constant depending on \(r,\eta,\pi\), giving \(O_{\pi,\eta,\epsilon}((Nd)^\epsilon)\) in total for arbitrary \(\epsilon>0\). The finitely many ramified factors cause no difficulty under the stated local bounds.

Mellin inversion now shifts the line to \(1/2+\eta\). The reciprocal \(1/L(s,\pi)\) is holomorphic there and polynomially bounded on the closed strip to its right, as follows from the fixed-\(\pi\) zero-free half-plane under RH and the standard logarithmic derivative bound a fixed distance from the zeros. A pole of \(L\) would give a zero of its reciprocal. The Mellin transform of \(V\) decreases faster than any power. The factors \(w(d),K_0^{-1}\) are \(O_\epsilon(N^\epsilon)\) as in the prior report. Taking auxiliary \(\epsilon\)'s small proves (7). For the unsigned reference weight \(w(n)/K_0\), removing \((-1)^j\) gives instead \(L(s,\pi)\) times a product with the same convergence, by cancellation of the linear coefficients at good primes. For cusp forms of degree at least two this standard \(L\)-function is entire. The same shift bounds the unsigned reference, proving the individual estimates. Finally sum \(N^\eta(N/d)^{1/2+\eta}\) over the stated range (it suffices to take \(\eta<1/2\)). ∎

**Scope.** The variable tested in (7) is \(n=N-p\) *in the sieve notation*. The automorphic coefficient is evaluated multiplicatively at \(n\). The conclusion also applies to a fixed Dirichlet character in the difference estimate. It adds genuinely new tests to the synthetic example. It does not assert that the model matches the genuine shifted primes for arbitrary observables. In particular \(\operatorname{Frob}_{N-n}\) on the reflected prime coordinate is not a multiplicative coefficient in \(n\); it is defined only at unramified primes. Even the original model requires the prior report's local modification to reproduce arbitrary prescribed finite sets of reflected reduced residue classes. There is no construction here matching all growing-field Chebotarev tests on that coordinate or the off-diagonal in (4). Conversely, none of (1), the spectral hypotheses or the 2026 results supplies that off-diagonal for the true prime sequence. A parity model can refute a deduction from specified tests without modeling all consequences of ERH.

### A subcritical sieve reduction with one marked divisor

There is a way to move the cutoff below \(N^{1/4}\), retain the positive lower sieve, and charge every surviving odd composite to a **single range of divisors**. This gives a test on all rough complements without first recognizing primes or semiprimes. Here are the weight, a numerical threshold in closed form, and the unproved part of the test.

Set \(z=N^{2/9}\). Sum over primes \(p<N\) with \(p\nmid N,\ m=N-p>1,\ P^-(m)>z\), and denote this summation by \(\sum^R\). Put
\[
 \begin{split}
 V_N(z)&=\prod_{\ell\le z,\ \ell\ {\rm prime},\ \ell\nmid N}
                 (1-1/(\ell-1)),\\
 J(m)&=\#\{r\ {\rm prime}:z<r\le N^{1/3},\ r\mid m\},\\
 H(N)&=\sum\nolimits^R(\log p)
      \{\lambda(m)+(1-\lambda(m))J(m)\},\\
 f_*&=\frac{8e^\gamma}{9}\log(5/4).
 \end{split}
\]
**Proposition.** Under Dirichlet GRH, for each fixed \(\epsilon>0\) and all sufficiently large even \(N\), the single inequality \(H(N)\le(f_*-\epsilon)NV_N(z)\) implies
\[
        \sum_{p+q=N,\ p,q\ {\rm prime}}\log p
            \ \ge\ \tfrac14\epsilon NV_N(z).
 \tag{8}
\]

**Proof.** Use the dimension-one lower linear sieve on the sequence \(m=N-p>1,\ p\nmid N\) with mass \(\log p\). For squarefree \(d\) coprime to \(N\) its divisor mass is \(N/\varphi(d)+O(\sqrt N L^2)\), uniformly for \(d\le\sqrt N\), by Dirichlet GRH. Omitting \(p\mid N\) and \(m=1\) costs \(O(L)\) in each test. The sieve omits primes dividing \(N\), since none can divide \(m\) on this sequence. Its dimension-one product bound is uniform in \(N\): deleting Euler factors for primes dividing \(N\) only decreases the inverse product over any sieving interval, and the full product over odd primes satisfies the linear-sieve bound by Mertens' theorem. Also \(V_N(z)\gg1/\log z\). Take \(D=\sqrt N/L^{10}\); the absolute remainder is \(O(N/L^8)\). The lower linear sieve gives
\[
       S_z:=\sum\nolimits^R\log p
        \ge (f_* -o(1))NV_N(z),
\]
since \(\log D/\log z\to9/4\) and \(f(s)=2e^\gamma\log(s-1)/s\) for \(2<s\le4\). Including a prime exactly at the real cutoff amounts to using the sieve product through \(z\).

Every \(m\) counted has at most four prime factors with multiplicity. If \(\lambda(m)=-1\) and \(m\) is composite, it has three, so its smallest factor is at most \(m^{1/3}<N^{1/3}\), and \(J(m)\ge1\). Therefore, term by term,
\[
     (1-\lambda(m))(1-J(m))\le 2\,1_{\mathbb P}(m).
\]
This includes cubes, repeated factors and primes in the marked range. Multiplying by \(\log p\) gives \(2\sum_{p+q=N}\log p\ge S_z-H(N)\). Taking the sieve error below \(\epsilon/2\) proves (8). ∎

The threshold in (8) comes from a divisor estimate independent of Goldbach. Its marked term can be written as a sum over \(z<r\le N^{1/3}\) of rough parity sums on \(p\equiv N\bmod r\). It charges only the odd sign and may overcount composites, so this test is sufficient and can lose more than the exact prime count. Neither GRH for the single progression nor the Lü–Wang–Wu theorem bounds the resulting \(H(N)\). In particular (6) applies to this choice of \(z\) as well. This gives a precise alternative to assuming that lowering the cutoff by itself resolves the problem.

### A one-sided reduction with a proven supply of Chen candidates

One can avoid the unknown positive lower bound at the cube-root cutoff. Use the classical quantitative form of **Chen's Goldbach theorem**: for sufficiently large even \(N\), the number of \(p<N\) for which \(m=N-p>1\) has at most two prime factors counted with multiplicity is \(\gg \mathfrak S(N)N/L^2\), with an absolute implied constant. Here one can use \(\mathfrak S(N)=2\prod_{\ell>2}(1-(\ell-1)^{-2})\prod_{\ell\mid N,\ell>2}(\ell-1)/(\ell-2)\). In particular this factor is bounded below by a positive constant. Only this classical counting input is needed below. The supplied \(1+1.9\) existence statement alone would not justify such a counting bound on its narrower set.

Let \(\mathcal C_N\) be this set of primes \(p\), with square complements removed, and \(B_C(N)=\sum_{p\in\mathcal C_N}\mu(N-p)\). There are absolute \(c>0\), \(N_0\), independent of \(N\), such that
\[
 \#\{(p,q)\in\mathbb P^2:p+q=N\}
 \ \ge\ \tfrac12\big(c\mathfrak S(N)N/L^2-B_C(N)\big)
 \qquad(N\ge N_0).                                                \tag{9}
\]
Indeed at most \(\sqrt N\) candidates were removed, so Chen gives \(|\mathcal C_N|\ge c\mathfrak S(N)N/L^2\) after reducing its constant. On this squarefree set \((1-\mu(m))/2\) is the prime indicator. Every prime representation belongs, giving the exact count \((|\mathcal C_N|-B_C(N))/2\) before using Chen. Thus the **one-sided** condition \(\limsup_{N\to\infty,\ 2\mid N} B_C(N)L^2/(\mathfrak S(N)N)<c\) suffices for pointwise Goldbach for all sufficiently large even integers. A fixed fractional upper saving \(B_C(N)\le(1-\epsilon)|\mathcal C_N|\) also gives \(\gg_\epsilon\mathfrak S(N)N/L^2\) representations.

The content of (9) beyond the indicator identity is its **independent, uniform positive baseline**. It changes the signed test from cube-root rough complements of unknown lower mass to the full Chen set with established lower mass. The missing input is cancellation, or even a sufficiently small positive bias, for Möbius after selecting these candidates. The unrestricted Lü–Wang–Wu statement does not give it. Replacing \(\mathcal C_N\) by Li–Liu's smaller set would require its own quantitative supply and bias estimates. No explicit \(c,N_0\) are derived here. Even a proof of the asymptotic bias condition would require an effective threshold and a finite bridge to \(C\), or a separate argument covering that bridge, for an all-even result.

### Other 2026 inputs and the pointwise quantifier

The supplied Li–Liu fourth-moment estimate \(E_\pm(X)\ll X^{1/2}(\log X)^{100}\) permits an isolated exceptional target. The polynomial-value and square exceptional estimates of Althöfer–Chen–Perelli–Pintz and Perelli–Pintz still permit exceptions in their respective families. Linnik–Goldbach with five powers of two under GRH gives a representation after additive shifts. A representation with shift zero is not forced. Tian–Yang count signs of \((-1)^{\omega(m)}\) on both summands among integers. A value \(-1\) allows arbitrarily many distinct prime divisors of odd total number, and their theorem imposes no prime condition on either summand. Sun–Wang's argument bounds, Hong's Hecke moments, Hua–Yang's zero statistics, and Guo's short-interval Waring–Goldbach estimates concern other families, averages or numbers of summands. In the supplied statements none estimates (4), the rough \(B\) of (5), \(H(N)\) in (8), or \(B_C(N)\) in (9) for every even target. The withdrawn elementary claim is excluded.

**Source scope.** The exact fixed-shift theorem, Remark 3 and equations (2.12)–(2.13) were checked in the local Lü–Wang–Wu manuscript, arXiv:2610.20242v2. Other 2026 statements are used at the strength of the supplied dossier. The classical analytic ingredients in the new calculations are the Artin/Dirichlet explicit formula under the indicated hypotheses, the divisor Voronoi formula and Weil bound, Mellin inversion, the dimension-one linear sieve and quantitative Chen. The three conditional reductions in the prior report retain their own explicit endpoint. The signed estimates required for (8) and (9) remain open.
