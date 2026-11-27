# The switched Goldbach sieve at level one, and a signed Type II range

[P] For the Wave 3 lower linear sieve minus the separate upper sieves on rough composite complements, the supremum of the normalized margin at level one is **zero**. Every cutoff exponent \(1/3\le\beta\le1/2\) attains it. Below \(1/3\) the deficit is exactly twice the three-factor mass integral. The first formal positive level has infimum \(1\). The ordinary progression hypothesis used for this extrapolation is false at every fixed level above one.

[P] A different, signed comparison theorem would suffice at Bombieri–Vinogradov (BV) Type I level. In the Ford–Maynard framework a genuine Type II estimate on the smaller factor from \(N^{0.4383}\) to \(\sqrt N\) would already give a positive proportion of the comparison prime mass. For this abstract framework an explicit prime-free construction rules out any band starting above \(N^{0.475602034395}\) at the same Type I level. With Type I available at **every** fixed exponent below one, any fixed positive width at the balanced end suffices. [U] The sharp fixed-BV positivity threshold between the two bounds and the genuine shifted-prime Type II estimate remain unresolved. Binary Goldbach remains open, including under Dirichlet ERH.

[Q] Tags mark transcribed source statements. [P] marks derivations and executed computations, [I] interpretations, and [U] unproved inputs or unresolved conclusions. These are mathematical research results without a Lean verdict. [Wave 3](B004_B015_W3_PERSISTENT_THRESHOLD_PUSH.md) · [Wave 2](B003_B012_ASTRA_DISPERSION_PROJECTION.md)

## 1. The two sieve coefficients

[P] Take even \(N\to\infty\), \(u=1/\beta\in[2,5]\), and use the unit \(X_N=\mathfrak S(N)N/\log N\), with \(\mathfrak S=2C_2\prod_{\ell\mid N,\ell>2}(\ell-1)/(\ell-2)\). Sum \(\log p\) over primes \(p\nmid N\) with \(m=N-p>1\) and least prime factor \(>N^\beta\). Denote the total by \(S_z\), its \(\Omega(m)=k\) part by \(P_k\), and set \(P_k=0\) for an empty layer. Strict roughness forces \(k<1/\beta\) at an integral endpoint. Exactly \(P_1=S_z-\sum_{k=2}^4P_k\).

[U] The *common-level assumption* means that both the prime sequence and each ordered rough product sequence have the progression remainder estimates used by their respective linear sieves through \(D=N^\theta/\log^B N\) (or through every strictly smaller fixed exponent). A sufficient version sums absolute errors for squarefree \(d\) coprime to \(N\), relative to the coprime mass divided by \(\varphi(d)\), with arbitrary logarithmic saving. For the shifted sieve the residue of the unsifted variable is \(N\bmod d\). The limit at \(\theta=1\) uses the family of exponents from below, with \(N\to\infty\) first.

[Q,P] BV gives the prime level \(1/2\) unconditionally. Individual Dirichlet-ERH bounds summed absolutely give the same exponent. Wave 3's bilinear large-sieve argument also gives the product level \(1/2\) for these fixed \(k\): partition into short multiplicative boxes and group \(k-1\) prime variables against the last prime. Both lengths exceed a fixed power, the grouped coefficients have bounded multiplicity on prime products, the short-conductor character sums factor, and the \(O_k(1)\) factors and polylogarithmically many boxes only change the log budget. Equal-factor and ordering boundaries may be covered by enlarged boxes. Their normalized total product mass error tends to zero as the mesh tends to zero. The upper sieve can be applied directly to the enlarged sequence. [Large-sieve estimate and boundary argument](B004_B015_W3_PERSISTENT_THRESHOLD_PUSH.md)

[Q,P] Ordinary EH concerns primes in progressions. Li–Liu's WEH uses a bounded weight \(f(r)\) on \(r\) times a **prime** with three specified endpoints and absolute errors after summing in \(r\). On fixed boxes one can group the other primes into \(r\), use their product multiplicity as a bounded weight (rescaling by \(k!\) if necessary), and difference the prime endpoints and the product endpoints. The last prime exceeds a fixed power, as the WEH ranges require. Common prime/product distribution remains a separate hypothesis when only ordinary EH is granted. BFI's \(4/7\), Maynard's \(3/5\) and Pascadi's \(5/8-o(1)\) concern specific weights on the moduli and residue hypotheses. Pascadi obtains the last exponent unconditionally with triply well-factorable weights. The \(2/3\) row below is a parameter test. None of these labels supplies the whole common-level hypothesis at the exponent in that row. [Li–Liu, §1.3](https://arxiv.org/html/2606.05224v2) · [Maynard](https://arxiv.org/abs/2006.07088) · [Pascadi](https://arxiv.org/abs/2505.00653)

[P] Define \(I_1(v)=1\) for \(v\ge1\), zero below. For \(k\ge2\), let \(I_k(v)=0\) for \(v\le k\) and otherwise put
\[
 I_k(v)=\frac1{k!}\int_{\substack{t_i\ge 1/v,\ \sum t_i=1}}
                 \frac{dt_1\cdots dt_{k-1}}{t_1\cdots t_k},
 \qquad I_k'(v)=\frac{I_{k-1}(v-1)}{v-1}.
 \tag{1}
\]
Here \(t_k=1-\sum_{i<k}t_i\), with projected simplex measure. Differentiating the \(k\) equal boundary faces and scaling the remaining coordinates by \(1-1/v\) gives the recurrence. In particular \(I_2(v)=\log(v-1)\) for \(v\ge2\). The PNT and partial summation give \((I_k(u)+o(1))N/\log N\) products of \(k\) rough primes below \(N\): sum the last prime first, with endpoint \(N/(q_1\cdots q_{k-1})\), then integrate the reciprocal-prime measures of the other factors. The product boundary determines \(t_k\). Permutations account for \(k!\), and repeated factors cost \(O_k(N\sum_{n>N^\beta}n^{-2})\). Units at primes dividing \(N\) introduce negligible exceptions or already vanish in the sifted sequence.

[P] Write \(E(v)=\sum_{j\ge1}I_{2j}(v)\) and \(O(v)=I_1(v)+\sum_{j\ge1}I_{2j+1}(v)\). The classical dimension-one functions satisfy \(sf(s)/(2e^\gamma)=E(s)\) and \(sF(s)/(2e^\gamma)=O(s)\) on their sieve ranges. Indeed \(E=0\) through 2, \(O=1\) from 1 through 3, and (1) gives precisely the two linear-sieve delay equations. This implements all the Buchstab iterations, including the \(I_4\) and \(I_6\) terms for larger \(s\). By Mertens, \(V_N(N^b)\sim e^{-\gamma}\mathfrak S(N)/(b\log N)\) for fixed \(b>0\). In units \(X_N\) the two bounds are
\[
 \liminf S_z/X_N\ \ge L(\beta,\theta)=\frac2\theta E(\theta u),\qquad
 \limsup \sum_{k=2}^4P_k/X_N\ \le U(\beta,\theta)
       =\frac2\theta C(u),\quad C(u)=I_2(u)+I_3(u)+I_4(u).
 \tag{2}
\]

[P] For the second inequality, sieve \(N-q_1\cdots q_k\) with cutoff \(N^b\). Its coefficient on \(I_k\) is \(e^{-\gamma}F(\theta/b)/b=2O(\theta/b)/\theta\) for \(\theta/b\ge1\). Its minimum \(2/\theta\) is reached throughout \(1\le\theta/b\le3\), e.g. \(b=\theta/2\). Prime outputs below this cutoff cost \(O_k(N^b\log N)=o(X_N)\), by unique factorization. Weighting the rest by at most \(\log N\) gives (2). For replacing the coprime product mass in the main term, primes in a product exceed \(N^\beta\), and \(\sum_{d\le D,\ v\mid d}1/\varphi(d)\ll\log D/(v-1)\) for prime \(v\). This gives a power saving after summing over products. The coefficients in (2) are exact for these two inequalities. They bound the genuine masses one-sidedly. Other Chen decompositions can correlate the two estimates differently.

## 2. Complete sign diagram

[P] Let \(M=L-U\). At level one, \(E(u)=I_2(u)+I_4(u)\) on the whole interval, hence
\[
 M(\beta,1^-)=-2I_3(1/\beta),\qquad
 \sup_{1/5\le\beta\le1/2}M(\beta,1^-)=0.
 \tag{3}
\]
The zero set is \([1/3,1/2]\). At \(\theta<1\), strict increase of \(E(v)\) above \(v=2\) gives \(M<0\) at every \(\beta<1/2\); \(M(1/2,\theta)=0\). The trivial bound \(P_1\ge0\) can always be adjoined. The negative entries below quantify the loss in the two separate estimates.

[P] At \(u>2\), the formal sign boundary is the unique \(\theta_c(u)\) solving \(E(\theta_c u)=C(u)\). It is exactly 1 for \(2<u\le3\), and lies strictly between 1 and \(3/2\) for \(3<u\le5\). For the upper endpoint use \(I_3(5)+I_4(5)<\log(13/8)\) and \((1.5u-1)/(u-1)\ge13/8\). The sign is positive on the higher-level side. At \(u=2\), \(M\) is zero through level 1 and positive thereafter. Thus the first positive level has **infimum 1**, with no least positive-margin level.

[P] In fact the formal maximizer at every \(1<\theta\le3/2\) is uniquely \(\beta=1/2\), and its margin is \(2\log(2\theta-1)/\theta\). Here are details of the optimization. Write \(x=\theta u-1\), \(H(x)=I_3(x)+I_5(x)\), \(K(u)=I_2(u-1)+I_3(u-1)\). The derivative of \(E(\theta u)-C(u)\) is \(\theta(1+H(x))/x-(1+K(u))/(u-1)\). It is strictly negative if \(H(x)<K(u)+(\theta-1)/[\theta(u-1)]\). For \(2\le u\le3\), \(H\le(x-3)_+^2/4\le(\theta-1)^2/4<(\theta-1)/(4\theta)\), using (1) and \(\theta\le3/2\). From \(u=3\) to 5, \(K'(u)\ge1/2\): for \(t=u-2\in[1,2]\) it is \(1/t\), and for \(t\in[2,3]\) use \(\log(t-1)\ge(t-2)/2\). On \(x\le6.5\), \(I_3'(x)\le0.3\) by \(\log y/(1+y)\le0.3\) for \(y\ge1\). Consequently \(I_4(5.5)\le(0.3/3)(1.5)^2/2=0.1125\), so \(I_5'(x)\le0.1125/4\). Thus \(\theta H'(x)<1/2\). The bound at \(u=3\) propagates as \(H<K+(\theta-1)/(4\theta)\), which suffices throughout.

[P] **Arithmetic obstruction.** For each prime modulus \(N<q\le N^{1+\delta}/\log^B N\), no positive shifted integer \(N-p<N\), or \(N-q_1\cdots q_k<N\), is divisible by \(q\). The predicted progression mass is the full underlying mass divided by \(q-1\). The sum of these reciprocal moduli tends to \(\log(1+\delta)>0\). Thus the absolute remainder sum is at least a fixed fraction of the mass already on prime moduli, even in the single required residue. This rules out the input that made the upper half of the diagram formal. BFI's advance was beyond the square-root exponent.

| [P] Common \(\theta\) | \(M(1/5,\theta)\) | \(M(1/4,\theta)\) | \(M(1/3,\theta)\) | \(M(2/5,\theta)\) | \(M(1/2,\theta)\) |
|---:|---:|---:|---:|---:|---:|
| \(1/2\) | −5.607229 | −4.983332 | −2.772589 | −1.621860 | 0 |
| \(4/7\) | −4.158816 | −3.480815 | −2.426015 | −1.419128 | 0 |
| \(3/5\) | −3.713751 | −3.031202 | −2.310491 | −1.351550 | 0 |
| \(5/8\) | −3.371202 | −2.689177 | −2.218071 | −1.297488 | 0 |
| \(2/3\) | −2.879923 | −2.205022 | −2.079442 | −1.216395 | 0 |
| \(0.999\) | −0.815868 | −0.297407 | −0.003005 | −0.003339 | 0 |
| \(1^-\) | −0.812183 | −0.294441 | 0 | 0 | 0 |
| \(1.001\), formal | −0.808507 | −0.291485 | 0.002995 | 0.003327 | 0.003992 |
| \(1.25\), formal | −0.084479 | 0.248556 | 0.509526 | 0.557291 | 0.648744 |
| \(1.5\), formal | 0.397598 | 0.584492 | 0.749453 | 0.808181 | 0.924196 |

[P] The formal roots at \(\beta=1/5,1/4\) are \(1.287589856870435\) and \(1.117154623821671\). At \(1/5\), the separate \(I_2,I_3,I_4\) entries are \(1.386294361,\ 0.406091633,\ 0.014886347\). [Phase diagram](/tmp/astra_w4_sieve/phase.svg) · [Executable interval calculation](/tmp/astra_w4_sieve/phase.py)

## 3. How much signed information would suffice?

[P] **One semiprime band near full level.** Fix \(1/3\le\beta\le a<b\le1/2\), and put \(J_{ab}=\log[b(1-a)/(a(1-b))]\). Suppose an independent upper estimate on *genuine* \(p+qr=N\) with smaller prime \(N^a<q\le N^b\) costs \(cJ_{ab}X_N\) asymptotically. For \(2\beta<\theta\le1\), apply the switched upper sieve only outside that band. The surviving coefficient is
\[
 \frac2\theta\log\frac{\theta-\beta}{1-\beta}
       +\left(\frac2\theta-c\right)J_{ab}.                         \tag{4}
\]
This follows by subtracting the replaced portion from (2). At the limiting level one, **any fixed \(c<2\) on any fixed band of positive width suffices**, by continuity at a strictly subunit level. For a central band take \(\beta=a,b=1/2\); there are then no remaining composite bands and ordinary prime EH suffices for the unsigned side of (4). The Hardy–Littlewood prediction is \(c=1\). Only the one-sided saving is required. [U] The saving for real shifted primes is missing.

[P] **Why the coefficient class matters.** A Type II asymptotic needs a main term that retains congruences in *both* variables. For example, when \(3\nmid N\), coefficients selecting \(d\equiv1,\ k\equiv N\bmod3\) select reflected multiples of 3. Against \(\Lambda(N-dk)\) almost all such pairs have zero weight. A uniform product-of-means replacement would give positive density. The Wave 2 projection with a single Liouville column and the usual unrestricted Selberg square or multidimensional Maynard weights supply no comparison for general signed rows and columns. Divisor-supported minorants and squared weights that expand only into matched Type I tests give the same estimates on the prime-free parity model to their allowed modulus level. [Wave 2, §4](B003_B012_ASTRA_DISPERSION_PROJECTION.md) · [Local parity model](B003_PARITY_ANALYSIS.md)

[Q,P] A precise strong comparison hypothesis uses \(x=N\), \(x/2<m\le x\), \(a_m=\Lambda(N-m)\), with weight zero at nonpositive arguments, and \(w_m=a_m-b_m\) for a nonnegative locally matched comparison \(b\). Require the following estimates uniformly in even \(N\), with arbitrarily large logarithmic saving after allowing fixed divisor powers in the weights:
\[
 \sum_{d\le x^{\theta_1}}\tau(d)^B\max_I
 \left|\sum_{\substack{k\in I\\x/2<dk\le x}}w_{dk}\right|\ll x/\log^B x,
 \qquad
 \left|\sum_{d\text{ in band}}\sum_{x/2<dk\le x}\xi_d\kappa_k w_{dk}\right|
 \ll x/\log^B x,\quad |\xi_d|,|\kappa_d|\le\tau(d)^B .
 \tag{5}
\]
Assume the mild growth condition (w), \(\sum b_p\gg x/\log^{O(1)}x\), and the rough-product PNT for the comparison, (b.2) of Ford–Maynard. Their \(C^-\) is the best guaranteed lower ratio \(\sum a_p/\sum b_p\) in this class. A positive constant suffices because the contribution of reflected proper prime powers to \(\sum a_p\) is \(O(\sqrt N\log^2 N)\). [Ford–Maynard, §§1, 4 and 7](https://arxiv.org/pdf/2407.14368)

[P] One concrete comparison is \(b_m=(W/\varphi W)\mathbf1_{(N-m,W)=1}\), with \(W\) the product of primes through \(y=(\log N)^H\) and \(H\) large for each prescribed error budget. On a unit row \(d\) the small-prime sieve for \(k\) has one forbidden class at each \(\ell\le y,\ell\nmid d\); its normalized density is \(\prod_{\ell\mid d,\ell\le y}\ell/(\ell-1)\). The ratio to \(d/\varphi(d)\) differs from one by \(O(\log N/(y\log y))\). A nonunit row vanishes in the model if its common factor contains a prime through \(y\). The total main mass of the other nonunit rows is \(O(N\log^{O_B(1)}N\sum_{\ell\mid N,\ell>y}1/\ell)\). The genuine nonunit terms come from prime powers dividing powers of primes of \(N\) and cost \(N^{o(1)}\) including row multiplicities. On reduced rows, weighted BV follows by Cauchy–Schwarz from BV with a larger log budget and the trivial progression bound \(O(N\log N/d)\). These give Type I for any fixed \(\theta_1<1/2\); prime EH gives its corresponding subunit levels. For the model on a row use the fundamental lemma with a small fixed-power sieve level depending on \(1-\theta_1\); rounding costs at most that level times log powers per row, and \(\log D/\log y\to\infty\) fast enough for arbitrary log savings.

[P] For \(\sum b_p\), sieve \(N-p\) only through \(y\) using BV and the fundamental lemma. The normalized local factors are \(\ell/(\ell-1)\) at \(\ell\mid N\) and \(\ell(\ell-2)/(\ell-1)^2\) otherwise. Their product is \(\mathfrak S(N)(1+o(1))\) uniformly, so \(\sum b_p\sim\mathfrak S(N)x/(2\log x)\). The same calculation gives (b.2) for ordered products of a fixed number of primes all exceeding \(x^{\nu-o(1)}\), \(\nu>0\) fixed: partition exponent space into small boxes, freeze all factors except one, and apply maximal BV to that last prime at a level \(x^{c}\) with \(0<c<\nu/2\). The other factors are coprime to \(W\). After the fundamental lemma the same local product multiplies every box. The ordinary product PNT gives the simplex measure in (1). To obtain the fixed \(1/B\) error in (b.2), approximate Lipschitz tests by constants on a fixed sufficiently fine mesh; the boundary layer of a convex region in the bounded simplex has volume \(O_k(\text{mesh})\), and the density is bounded away from the coordinate hyperplanes. One may subdivide boxes in the prime variables by log powers and keep the product interval in the last prime, so summed BV errors lose at most log powers. The growth condition follows from the polylogarithmic pointwise bound on \(a_m,b_m\). [U] What remains in (5) for this comparison is the genuine Type II discrepancy. The prime-erasure example preserves boxes on products but also changes the prime-level mass and the Type I comparison.

[P] If \(\theta_1>2\alpha\), (5) on the smaller factor from \(x^\alpha\) to \(x^{1/2}\) suffices even for an asymptotic. Vaughan cutoffs \(U=V=x^{\alpha+\epsilon}\) give \(UV<x^{\theta_1}\); the two Type I terms, including the log-weighted inner progression, are controlled by the first estimate and partial summation. Both variables in the remaining signed term exceed \(x^\alpha\), one is at most \(\sqrt x\), and the diagonal/order cut can be separated at logarithmic cost by Perron/Fourier truncation (or included as interval-uniformity). The short term vanishes on the support for \(V<x/2\). Applied to \(w\), this compares \(\Lambda\)-weighted sums, with an interval-uniform version or the Ford–Maynard theorem giving the prime comparison. For the EH family, choose \(2\alpha<\theta_1<1\). Thus the exact **supremum** of sufficient lower endpoints is \(1/2\) in this family. At zero width the argument supplies no Type II information. For a **single** fixed \(\theta_1<1\), Ford–Maynard Theorem 2.1 constructs prime-free examples for sufficiently narrow bands. Their Theorem 2.2 at ideal Type I \(1/2\) gives \(1/3\) as the exact central lower endpoint for a guaranteed *asymptotic* (the obstruction beyond it is the triple \(1/3,1/3,1/3\)). Their Theorem 2.7 on \([0,\nu]\) treats a different band. [Ford–Maynard, Theorems 2.1–2.2](https://arxiv.org/pdf/2407.14368)

## 4. Quantitative bounds on the BV Type II positivity endpoint

[P] Here \(a\) denotes a **factor exponent**, \(\nu=1-2a\), and the symmetric Type II interval is \([a,1-a]\). Use the Ford–Maynard parameters \((\gamma,\theta,\nu)=(1-a,a,1-2a)\). The interval is supplied by (5) on the smaller factor: transpose the factors above \(\sqrt x\). Type II also gives Type I on these rows by taking a constant column and using their Proposition 4.11 for the interval maximum. BV-level Type I on smaller rows therefore suffices. Endpoint constants matter. The exact calculation below uses the displayed symmetric interval with the paper's endpoint conventions; a smaller-factor estimate down to \(x^a/2\) covers it. From a literal band \([N^\alpha,\sqrt N]\), use any fixed \(a>\alpha\) to absorb constant endpoint factors. A fixed \(\theta_1\) strictly between \(a\) and \(1/2\) covers the initial rows, so the BV log loss is harmless. [Ford–Maynard, Proposition 4.11](https://arxiv.org/pdf/2407.14368)

[P] **A three-prime obstruction and an exact special case.** For \(1/3<a<1/2\), put
\[
 J(a)=\frac1{3!}\int_{\substack{x+y+z=1\\0<x,y,z<a}}\frac{dx\,dy}{xyz}
 =\frac13\int_{1-2a}^a \frac{\log(a/(1-t-a))}{t(1-t)}\,dt .       \tag{6}
\]
Every such triple has individual components \(>\nu\), and every pair has sum \(>1-a\). It and its groupings avoid the Type II interval. Define a symmetric test \(h_3=-1\) on these triples, zero elsewhere, and \(h_2(t,1-t)=\log(a/(1-t-a))\) for \(\nu<t<a\), using the smaller coordinate \(t\). Set \(h_1(1)=-2J(a)\), with all other entries zero. The Type I fragmentation identities (6.2) in Ford–Maynard hold directly. Fixing one coordinate \(t\le1-a\) of a contributing triple, the positive two-factor integral cancels the negative three-factor integral, since \(h_2/(1-t)=\int_{1-t-a}^{(1-t)/2} dv/[v(1-t-v)]\). No two fixed coordinates of a supported triple can sum to at most \(1-a\). With no coordinate fixed the two-factor integral is \(3J\), the three-factor integral is \(-J\), and the singleton supplies \(-2J\). These functions are bounded, piecewise Lipschitz, supported on permitted groupings, with coordinates bounded below. This verifies the hypotheses of their construction theorem for any \(\eta<\nu\).

[P] Ford–Maynard Theorem 6.3(b) now gives \(C^-\le\max(0,1-2J(a))\), by scaling \(h\) if needed. If \(2J>1\), 6.3(a) gives **actual prime-free abstract sequences**: its prime value is near \(-2J<-1\) while its composite values are at least \(-1-o_\delta(1)\). Rescale the negative prime value to \(-1\) and add the reference sequence \(b=1\). At equality the conclusion is \(C^-=0\). The root is unique by strict domain growth in (6), and certified quadrature gives
\[
 a_{\rm obs}=0.4756020343943107203\ldots,\qquad 2J(a_{\rm obs})=1.
 \tag{7}
\]
These examples have Type I through \(1-a\) and so also satisfy any weaker BV-scale requirement. The construction concerns the general comparison class; its weights have no asserted realization as \(\Lambda(N-m)\).

[P] For \(1/3<a\le2/5\), the upper bound \(1-2J\) is **attained** in this abstract extremal problem. To see the matching lower bound, use the minorant in Ford–Maynard Theorem 7.3(a). Its domain \(H\) consists of permitted groupings with at least two coordinates, all \(\ge\nu\), whose proper subsums avoid \([a,1-a]\). Each coordinate is small (\(<a\)) or large (\(>1-a\)). A large coordinate can accompany just one small one, since \(2\nu\ge a\). With all coordinates small, four or more are impossible: the two smallest sum to at least \(2\nu\ge a\) and at most \(1/2\). Thus the remaining case is exactly the triples in (6). Take \(g(\varnothing)=1,\ g(\text{small singleton})=-1\) and zero elsewhere. The total over subvectors is zero on the two-factor case and \(-2\) on the triples. The permitted small subvectors belong to \(G_1\): adding components \(<\nu\) cannot pass from below \(a\) across the entire forbidden interval of width \(\nu\), hence the total remains below \(a\le\gamma\). Theorem 7.3(a) proves the claim. In particular \(C^-(3/5,2/5,1/5)=0.81398834000028109\ldots\). [Ford–Maynard, Theorems 6.3 and 7.3](https://arxiv.org/pdf/2407.14368)

[P] **A narrower sufficient band.** For \(3/7\le a\le4/9\), use \(g(\varnothing)=1\), and on permitted small-total subvectors of sizes 1, 2, 3 respectively put \(-1,2/5,-1/10\); take zero elsewhere. These are admissible \(G_1\) weights by the same partial-sum argument. All coordinates in \(H\) are \(\ge\nu\), and \(4\nu\ge a\). For an all-small vector write \(s\) for the number of pairs with large total. The full subvector sum \(1\star g\) is as follows.

| [P] Configuration in \(H\) | \(1\star g\) | Count giving the value |
|---|---:|---|
| One large coordinate and \(j=1,2,3\) small | \(0,-3/5,-9/10\) | All subsets of the \(j\) coordinates have small total. |
| Three small | \(-2\) | All pairs have large total. |
| Four small | \(-9/5\) | Exactly three of the six pairs have small total, by complementation. |
| Five small | \(-s/2\) | There are \(10-s\) small pairs and \(s\) small triples. |
| Six small | \(0\) | All pairs are small and exactly ten triples are small. |
| Seven small | \(-11/10\) | All pairs and triples are small. |

[P] For six or seven components a complement containing at least four cannot be small. Eight or more are impossible by partition into two subsets of size at least four. This exhausts \(H\) and verifies the required nonpositivity pointwise. The following one-dimensional integrals bound the deficit in Theorem 7.3(a):
\[
 \begin{aligned}
 k(t)&=\frac{\log((t-\nu)/\nu)}{t(1-t)},&
 K&=\int_{2\nu}^{a}k(t)\,dt,&
 A&=\int_{2\nu}^{a}k(t)\log\frac a{1-t-a}\,dt,\\
 V&=\frac{(a-3\nu)^3}{36\nu^3(1-a)},\qquad
 D(a)&=1-2J(a)-\frac35(K+A)
       -\left(\frac9{10}+\frac12\log\frac a\nu\right)V
       -\frac{11}{10}I_7(1/\nu).
 \end{aligned}                                                     \tag{8}
\]
Then \(C^-\ge D(a)\). For two small and one large coordinate, integrate over the small pair's total \(t\); its ordered density gives \(K\). Each all-small four-vector has three small pairs. Marking a small pair and integrating over its complementary ordered pair costs at most \(A\), giving a total cost at most \(3A/5\). For three small coordinates with total \(t<a\), their ordered volume is \((a-3\nu)^3/(3!)^2\), and the reciprocal denominator including the large complement is at most \(1/[\nu^3(1-a)]\). This gives \(V\). For five small coordinates mark a large pair; its complementary triple is small, and splitting the large coordinate into two factors \(<a\) multiplies its density by at most \(\log(a/(1-t-a))\le\log(a/\nu)\). Finally enlarge the seven-factor region to the full rough simplex. All enlargements bound nonnegative loss terms.

[P] At \(a=0.438\), \(D=0.0156483689840682391\ldots\); at \(a=0.4383\), \(D=0.0022248207212302554\ldots\). The root of this explicit minorant coefficient is \(a_{\rm suff}=0.4383492128014972105\ldots\). The loss terms increase on this range by their positive-integral representations and the monotonicity of their domains or factors. For a literal starting exponent \(0.4383\), choose \(a\) strictly between \(0.4383\) and the root. Combining (7) and (8), the supremum of endpoints guaranteeing positive proportion in the abstract BV-level, central-band comparison satisfies
\[
       0.4383492128014972105\ldots\ \le\ \alpha_{\rm pos}\
       \le\ 0.4756020343943107203\ldots .
 \tag{9}
\]
[U] An equality closing this interval would require a stronger minorant or a stronger obstruction. The exponents alone in the original uncentered bilinear expression do not define a unique optimization over all Goldbach-specific methods. The fixed comparison class above makes (9) a testable substitute.

[P] For comparison, at the ideal single Type I exponent \(0.999\), Theorem 2.2's exact full-asymptotic boundary on the central band is \(500/1001=0.4995004995\ldots\). In its (A1), the first odd denominator at least \(1001\) gives the smallest fraction \(\lfloor n/2\rfloor/n\) among those denominators. In (A2), \(500(1-0.999)=1/2\). Strictly interior bands handle logarithmic endpoint losses by taking a slightly smaller Type I exponent. This is an asymptotic threshold under the *independent signed* (5). The positivity-only optimum at that fixed level can differ. For the EH family the supremum \(1/2\) from §3 is exact.

## 5. What each route still requires

| Route | [P,Q] Sufficient pointwise input | [I,U] Scope |
|---|---|---|
| Circle method, B-011/B-002 | Under named Dirichlet ERH take \(Y=(\log N)^4\). In the H2 normalization it suffices that \(\Re\int_{B} S_{<Y}^2e(-Nt)\,dt\ge-N/3+b(Y,N)\), where the high-zero deletion error is bounded by \(b=O(N/\sqrt{\log N})\). | This is a signed estimate at each even target including pole, residues and cross terms. The high-zero truncation leaves the low-zero problem. [Wave 3 circle analysis](B011_W3_PERSISTENT_BETA_PUSH.md) |
| Switched sieve / Type II, B-005/B-012 | At near-unit common level, (4) states the exact saving needed on one semiprime band; for the full EH family and a central band, prime EH plus any fixed cost \(c<2\) suffices. At BV level, the signed comparison (5) from exponent \(0.4383\) suffices. | The semiprime input is one-sided on a specific statistic. The general signed comparison imposes many more tests but can use known BV-scale Type I. Both require new information about the shifted primes. |
| Chen / Li–Liu, B-015 | With \(T=G+U_2,\ B=U_2-G\) on primes and distinct semiprimes, \(B<T\) is exactly \(G>0\). A known supply \(T\ge c\mathfrak S N/\log^2N\) makes \(B<(c\mathfrak S N/\log^2N)\) sufficient. The cited \(1.4\) supply under WEH(0.999) has \(c=0.031\) in these units. | The quantitative Chen supply is available eventually with a positive constant. The \(1.4\) supply is an external input; neither supplies the required bias. [Sieve comparison](B015_B005_SIEVE_NARROWING_ATTACK.md) |
| GWX, B-004 | Under the detector's other hypotheses, a uniform moving-line norm saving over the necessary conductors suffices for a Hardy–Littlewood asymptotic. On Wave 3's balanced test at \(q=N=2^k\) and \(q=p^2,N=2q\), \(T_\eta=o(q^{1-2\eta})\) is equivalent to the tested \(R(N)=o(N)\), with ERH used on the finer square grid. | The signed test at these sparse conductors identifies a necessary local obstacle for that line of attack. Extending it to the full norm and all targets is a separate assumption. [Top-conductor calculation](B004_B015_W3_PERSISTENT_THRESHOLD_PUSH.md) |

[I] Bare \(B<T\) has the weakest logical conclusion in this table, since it is exactly positivity. Calling it the easiest new theorem would assume the desired sign. The narrow semiprime improvement has the most localized input here, conditional on near-full prime distribution. At the unconditional distribution level, (5) gives a concrete signed target. There is no established implication ordering these independent missing estimates by analytic difficulty. [U] None gives an unconditional or ERH-conditional proof. Even a uniform asymptotic positivity theorem would still require a finite bridge to cover all even \(N\ge4\).

## Numerical verification

[P] Run the local replay with the Python interpreter at the first link and the script at the second. The script uses 200-bit Arb balls. For (1) it integrates the method-of-steps Taylor series on meshes \(1/4\) and \(1/8\), to degrees 96 and 64. On the complex disk of radius \(3/4\) about a mesh point in an active analytic piece, successive integrations have amplification at most \(3\), since the denominators are at least \(1-3/4\). The real initial values are bounded by 10 on this domain, e.g. by \(I_k(v)\le(\log v)^{k-1}/(k-1)!\), by induction in (1). Thus \(10^5\) bounds the analytic extensions through \(k=7\). On a step \(h\), the Cauchy tail is at most \(10^5(4h/3)^{n+1}/(1-4h/3)\); the script carries it as an interval through all later steps. All tabulated phase enclosures overlap across meshes and have radius less than \(10^{-33}\) before rounding. For (6)–(8) the script also uses certified complex quadrature with analyticity checks and sign-tested bisection. Integrating (6) independently over the largest prime exponent reproduces the same balls at three cutoffs. The complete replay ran in under one second. The proofs provide exact integral expressions; the printed decimals are rounded enclosures. [Python interpreter](/tmp/astra_w2_b011/venv/bin/python) · [Verification script](/tmp/astra_w4_sieve/phase.py)
