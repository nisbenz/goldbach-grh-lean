# Wave 3 · The loss from narrowing, the rough cutoff, and the top conductor

[P] Switching onto a prime cofactor halves the fixed-factor Selberg coefficient from 8 to 4. Averaging the two prime factors before sieving gives a sharper loss, with break-even exponent $1+(a-1)e^{-c_a/4}$ at unconditional distribution level $1/2$. The strongest examples below are $1.899956$ with the reported unconditional supply and $1.393854$ with the reported conditional supply and WEH(0.999). [U] The supplies and WEH remain inputs. [P] At the rough cutoff $N^{1/5}$ the unsigned lower-sieve baseline increases by 81.706%. A fixed smooth test inside $mn<q^2$ still measures a single balanced Goldbach discrepancy after model subtraction at both sparse top conductors.

[Q] Notation follows the two Wave 1 reports. [P] labels a derivation or executed computation, [Q] a transcription, [U] an external paper input or missing bound, and [I] an interpretation. All three blockers remain open. These are research calculations without a Lean verdict. [Ratios audit](B004_B014_GWX_RATIOS_ATTACK.md) · [Sieve audit](B015_B005_SIEVE_NARROWING_ATTACK.md)

## 1. Upper-sieving the lost semiprimes

[P] Put $L=\log N, S=\mathfrak S(N), t_x=1-1/x$, and measure counts in units $SN/L^2$. For fixed $1<b<a<2$, discard $m=N-p<N/L^4$ at cost $O(N/L^4)$. A lost complement has prime factors $rn=m$, with $r$ in $(N/L^4)^{t_b}<r\le N^{t_a}$. Primes $r\mid N$ account for at most $\omega(N)$ original candidates. This enlarges the band by a log-power at its lower edge, with $o(1)$ normalized cost in the integral estimates below.

[P] **Fixed $r$.** Start with primes $n<X=N/r$. Sieve the values $N-rn$ at primes $\ell\nmid Nr$. The forbidden class is $n\equiv Nr^{-1}\pmod\ell$, reduced for every such prime. At squarefree $d$ supported there the main count is $\mathrm{Li}(X)/\varphi(d)$. Classical Bombieri–Vinogradov (BV) gives a summed absolute error $O_A(X/\log^A X)$ through $D=X^{1/2}/\log^B X$. Its maximum over reduced classes covers the varying inverse for **each** fixed $r$. Uniformity follows since $X\ge N^{1-t_a}$. Summation over prime $r$ uses $\sum_{r\text{ in band}}1/r=O_{a,b}(1)$.

[P] The dimension-one upper linear sieve at $z=D^{1/2}$ has $F(2)=e^\gamma$. Mertens gives the product $(1+o(1))e^{-\gamma} S_{N,r}/\log z$, with $S_{N,r}=S(r-1)/(r-2)$. Uniformity follows from the convergent ordinary singular-product tail and $O(\log(Nr)/\log z)$ prime divisors of $Nr$ above $z$, each correcting the product by $1+O(1/z)$. The inverse-product dimension bound only decreases on omitting primes. Prime outputs below $z$ cost $O(z+1)$ per $r$. Thus the upper bound is $(4+o(1)) S_{N,r} X/\log^2 X$, unconditionally, including $r$ near $N^{9/19}$ or $N^{2/7}$. GRH with termwise square-root remainders reaches the same power on the cofactor scale. No well-factorable estimate is needed for this step.

[P] Starting with $p<N$ and sieving $n=(N-p)/r$ tests $p\equiv N\pmod {rd}$. Ordinary BV controls **total modulus** $rd\lesssim N^{1/2}/L^B$ on average. At $r=N^u$ this leaves $d=N^{1/2-u-o(1)}$, with exponents $1/38$ and $3/14$ at the two upper band edges. The sum over pairs costs bounded multiplicity since a total modulus has $O_b(1)$ prime divisors in the band. Individual GRH errors $O(\sqrt N L^2)$ accumulated over these tests also do not give a larger absolute-error level. An assumed ordinary prime level $\theta>u$ changes the remaining power to $\theta-u$. This distinguishes the two choices of prime variable.

[P] For a uniform coefficient $C$ on the cofactor scale, retaining the denominator gives loss
$$
 C\int_{t_b}^{t_a}\frac{du}{u(1-u)^2}
 = C\left[\log\frac{a-1}{b-1}+a-b\right].
$$
The zero-margin root is $1+W((a-1)\exp(a-1-c_a/C))$, using the positive Lambert branch. A strictly larger $b$ is required. For $C=8$ the roots are 1.89998815794 and 1.39889395143. For $C=4$ they are 1.89997631595 and 1.39779009086. The integral improvement alone preserves the uniform coefficient.

### Averaging the product before the upper sieve

[P] Take the sequence of products $rn\le N$ in the enlarged band, both factors prime, with $rn\ge N/L^4$, and sieve $N-rn$. There is one forbidden reduced residue $rn\equiv N\pmod d$ for $(d,N)=1$. Its total main mass, up to $o(N/L)$, is
$$
 M=\sum_{r\text{ in band}}\mathrm{Li}(N/r)
   \sim \frac NL \int_{t_b}^{t_a}\frac{du}{u(1-u)} .
$$
This follows by the PNT and partial summation. Both factors exceed a fixed power of $N$ here. One may use the coprime mass $M_d$ of pairs prime to $d$ divided by $\varphi(d)$. Replacing it by the actual total pair mass divided by $\varphi(d)$ costs $o(N/L^A)$ in the *summed* error for each fixed $A$. For a factor $v\ge N^\delta$, $\sum_{d\le N,\,v\mid d}1/\varphi(d)\ll L/(v-1)$, and there are at most $O(NL)$ pairs. The actual total mass is $M+o(N/L)$, which suffices in the sieve main term.

[P] Here are level details for unconditional use of the bilinear large sieve. In a rectangle with prime variables of sizes $R,T\ge N^\delta$, $RT\ll N$, expand the progression discrepancy from the coprime mean in nonprincipal characters. Write the modulus as $kh$, with $h$ the primitive conductor. For fixed $k$, exclude primes dividing $k$ from each factor's coefficients. At $h\asymp H$, Cauchy–Schwarz and the multiplicative large sieve on each factor give a bound
$$
 \ll \frac{\sqrt{RT(R+H^2)(T+H^2)}}{H\varphi(k)}
 \ll \frac{RT/H+R\sqrt T+T\sqrt R+H\sqrt{RT}}{\varphi(k)} .
$$
This uses $\varphi(kh)\ge\varphi(k)\varphi(h)$ and holds for the maximum over reduced residues. Use $\sum_{k\le N}1/\varphi(k)\ll\log N$. For $L^K<H\le\sqrt N/L^B$, the first and last terms save arbitrary log powers by choosing $K,B$, and the middle terms save powers of $N$. Below $L^K$, Siegel–Walfisz gives arbitrary logarithmic savings for nonprincipal prime sums on both intervals, including endpoint differences. Excluding primes dividing $k$ costs $O(L)$ in each sum. The remaining conductor counts cost only log powers.

[P] To handle the product boundary, partition both variables at ratios $1+L^{-J}$ and keep every rectangle meeting the band and product constraints. There are $O(L^{2J+2})$ rectangles. The preceding error bounds absorb this for fixed $J$. The extra integer pairs at $rn=N$ or $N/L^4$ cost $O(NL^{1-J}+N^{t_a})$, by summing intervals of length $O(NL^{-J}/r+1)$. Include both $r$-endpoints as partition walls. Thus the enlarged sequence itself has level $D=\sqrt N/L^B$ and total mass $M+o(N/L)$ for $J>3$. Use nonnegative upper-sieve weights on the enlarged sequence, which can include a thin strip with $rn>N$. Cover actual positive prime outputs below $\sqrt D$ by $O(\sqrt D)$ original candidates. This proof uses standard BV-scale large-sieve and Siegel–Walfisz theorems, independently of the Li–Liu supply.

[Q,U] Li–Liu's WEH first inequality uses $R(y;d,A,m)=\#\{m\ell\le y:m\ell\equiv A\bmod d,\ \ell\text{ prime}\}-\mathrm{Li}(y/m)/\varphi(d)$, with $(m,d)=1$. Its bounded $f(m)$ can be the prime-band indicator. Set $x=N$, $1-\alpha=t_a$, and difference the cutoffs $y=N,N/L^4$. This grants the same progression input up to $D=N^{0.999}/L^B$ under the conjecture. Deleting the main terms with $r\mid d$ costs a power saving by the same reciprocal-modulus calculation. The article's named hypothesis thus applies directly to the product. Its truth and the two supply claims remain [U]. [Li–Liu, §1.3, (1.12) and Conjecture WEH](https://arxiv.org/html/2606.05224v2)

[P] Sieve the remaining affine form with $z=\sqrt D$ as above. Its product is $V_N(z)\sim e^{-\gamma}S/\log z$. For a product distribution level $D=N^{\theta-o(1)}$, the normalized loss has limsup at most
$$
 \frac{2}{\theta}\int_{t_b}^{t_a}\frac{du}{u(1-u)}
 =\frac{2}{\theta}\log\frac{a-1}{b-1}.
$$
The unconditional choice is $\theta=1/2$. Within a fixed band this even gives an effective coefficient at most $4(1-t_b)<4$ against the old integral with the squared denominator. The logarithm diverges as $b\downarrow1$. The break-even exponent is exactly $b_0=1+(a-1)e^{-\theta c_a/2}$ for this bound.

| [P] Supply $(a,c_a)$ [U] | Product level | Break-even $b_0$ | Strict example $b$ | Remaining normalized margin |
|---|---:|---:|---:|---:|
| (1.9, 0.0002) | 1/2 | 1.899955001125 | 1.899956 | 0.00000443966 |
| (1.4, 0.031), WEH supply only | 1/2 | 1.396911981528 | 1.39692 | 0.00008080775 |
| (1.4, 0.031), WEH also in loss | 0.999 | 1.393853907389 | 1.393854 | 0.000000470752 |

[I] These exponents quantify what the specified supply buys by continuity. Li–Liu separately mention a 1.894 refinement in the first case [Q,U]. The first row improves the Wave 1 continuity calculation. The second and third rows show exactly where using the conditional distribution assumption a second time helps.

## 2. The rough cutoff and its signed cost

[P] Let $R$ contain $m=N-p>1$, $p<N$ prime, $p\nmid N$, with least factor $>z=N^\beta$. Give it mass $\log p$, write $S_z$ for total mass and $G_R$ for its prime-complement mass. An composite with odd $\Omega(m)\ge3$ has a prime divisor $r\le m^{1/3}$, also when $\Omega=5$. Thus $(1-\lambda(m))(1-J_N(m))\le 2\mathbf1_{\mathbb P}(m)$ for $J_N=\#\{r\mid m:z<r\le N^{1/3},\ r\text{ prime}\}$ at every positive cutoff exponent. The cap $J=\mathbf1_{\exists\, r\mid m:\ z<r,\ r^3\le m,\ r\text{ prime}}$ marks every odd-parity composite and never a prime. With $H_J=\sum_R(\log p)[\lambda+(1-\lambda)J]$, one has exactly $H_J=S_z-2G_R$. At $\beta=1/5$ strict roughness and $m<N$ already force $\Omega\le4$. For $1/6\le\beta<1/5$ five factors may occur and the same mark covers them.

[P] With $D=N^{1/2}/L^{10}$ under Dirichlet GRH, $s\to1/(2\beta)$. Classical BV also supplies an unconditional level $\sqrt N/L^B$ for this particular unsigned sequence $N-p$, by the maximum over reduced residues, with prime log weights by partial summation. For $2<s\le5/2$, the lower coefficient is $f(s)=2e^\gamma\log(s-1)/s$. Its derivative has the sign of $s/(s-1)-\log(s-1)>0$. Uniformly at each fixed cutoff, $V_N(N^\beta)\sim e^{-\gamma}S/(\beta L)$, by the same product-tail argument as in §1. Thus $f(s)/\beta=4e^\gamma\log(s-1)$. The figures 1.444325 and 0.794870 are $sf(s)$, half the absolute coefficients before the Mertens factor.

| [P] $\beta$ | $f(s)$ | $f(s)/\beta$ | Baseline in units $SN/L$ |
|---:|---:|---:|---:|
| 2/9 | 0.353275400 | 1.589739298 | 0.892574205 |
| 0.201 | 0.568695509 | 2.829330892 | 1.588554661 |
| 1/5 | 0.577730176 | 2.888650882 | 1.621860432 |

[P] In the specified open interval the unsigned baseline has its supremum at $1/5^+$, attained on adjoining $1/5$. Relative to $2/9$, the coefficient $f$ grows by 63.535% and the absolute lower baseline grows by $\log(3/2)/\log(5/4)-1\approx81.706\%$. The *signed margin* $f-H_J/(NV_N)$ has no established asymptotic maximizer. For two nested rough sets with cutoffs $z_1<z_2$, the exact change in the capped observable is
$$
 H_{J,1}-H_{J,2}=(S_{z_1}-S_{z_2})-2(G_{R_1}-G_{R_2}),\qquad
 0\le G_{R_1}-G_{R_2}\le z_2 L .
$$
Consequently the additional capped signed mass tracks the actual additional unsigned mass to within $2z_2L$, negligible on the $SN/L$ scale. This quantifies why a stronger unsigned baseline alone gives no saving on prime pairs.

[P] Python/NumPy evaluated all 99,999 even targets $4\le N\le200000$ in 1.11 s locally. The algorithm uses exact integer cutoff comparisons, splits at changes to both lists of sieving primes, convolves with $\log p$, and removes $p\mid N$. A direct trial-division sum independently reproduced the original-mark ratios at 128, 149764 and 200000 within $10^{-14}$. The FFT sums are floating-point evidence. Run `python3 attack/src/scan_rough_cutoff.py` in a NumPy environment. [Replay script](../src/scan_rough_cutoff.py)

| [P] $\beta$ | Mark | $N$ with $H/(NV_N)\ge f$ | Maximum ratio on [100000,200000] | Margin $f-\max$ there |
|---:|---|---|---:|---:|
| 2/9 | original | 62, 122, 128, 134, 136, 1112, 1238 | 0.26326235 at 100094 | 0.09001305 |
| 2/9 | capped | 122, 128 | 0.14570049 at 101542 | 0.20757491 |
| 0.201 | original | 128, 152, 158, 212, 226, 232 | 0.45043449 at 149764 | 0.11826102 |
| 0.201 | capped | none | 0.26686264 at 144128 | 0.30183287 |

## 3. Smooth subtraction inside the critical box

[Q,U] Use the local subtraction identity (2) under its Dirichlet ERH setting and transcribed GWX model. For the top conductors considered here $\Delta=b_q(2)=0$. Thus $[E_q,W_N]=\sum_h b_q(h)R(h)$, where $R(h)=G_{q,W_N}(h)-\mathfrak S(h)F_N(h)$ and $F_N(h)=\int W_N(u,h-u)du$ on the positive line segment. This is subtraction before applying a norm. [Local subtraction identity](../../proof/strong_goldbach_persistent_push.md)

[P] Choose a fixed nonzero smooth nonnegative $g$ compactly supported in $(.29,.31)$, set $j(v)=g(1-v)$, and take the separable test $W_N(m,n)=g(m/N)j(n/N)$. Then $h/N\in(.98,1.02)$, $mn<.221N^2\le q^2$ for $N=q$ or $N=2q$, and $F_N(N)=N\int g^2>0$. The box excludes the integer diagonal. Define $T_\eta=N^{-1-2\eta}[E_q,W_N]$, the normalization of its double Mellin test on the two lines at $1/2+\eta$.

[P] **Dyadic target.** At $q=N=2^k, k\ge3$, the projector is supported on multiples of $q/2$. The window contains only $N$. Hence exactly
$$
 T_\eta=(q/4)N^{-1-2\eta}R(N).
$$
The actual term of $R(N)$ is the single sum $\sum_{(m(N-m),q)=1}\Lambda(m)\Lambda(N-m)g(m/N)^2$. A signed $o(q^{1-2\eta})$ estimate on this test is equivalent to $R(N)=o(N)$.

[P] **Odd prime square with a fixed smooth shape.** At $q=p^2,N=2q$, the primitive projector equals $\varphi(q)1_{q\mid h}-(p-1)1_{p\mid h}$. The $q$-grid contributes only $N$. For this test the finer $p$-grid satisfies
$$
 \sum_{p\mid h} R(h)=O_g(N\log^C N)\quad\text{under Dirichlet GRH}.
$$
Indeed the actual sum on that grid is a character sum modulo $p$, divided by $p-1$, of the products of two smooth prime sums with parity sign. The nonprincipal prime sums are each $O_g(\sqrt N\log^2 N)$ by the GRH explicit formula and partial summation. The principal contribution is $N^2(\int g)(\int j)/(p-1)+O_g(N^{3/2}\log^2 N/p+N\log^4N)$, and $N^{3/2}/p\asymp N$. The unit restriction for $q$ agrees with that for $p$.

[P] The model has the same mean to $O_g(N\log^C N)$. Only $h=2p k$ contribute. Write
$$
 \mathfrak S(2pk)=2 C_2\frac{p-1}{p-2}
  \sum_{d\mid k,\ (d,2p)=1}\frac{\mu^2(d)}{\prod_{\ell\mid d}(\ell-2)} .
$$
Writing $a_d$ for the positive divisor coefficient, the smoothed sum on the $2pd$-grid is $(2pd)^{-1}\int F_N+O_g(N)$ by bounded variation. For $d\le X\asymp N/p$, $\sum a_d\ll\log^C(2X)$ by the Euler product and Mertens, and $\sum_{d>X}a_d/d\ll\log^C(2X)/X$ by dyadic summation. The completed density is $1/(p-1)$, since $C_2\prod_{\ell>2}(1+1/[\ell(\ell-2)])=1$. Also $\int F_N=N^2(\int g)(\int j)$. This proves the grid estimate with constants independent of $p$.

[P] Combining the two grids yields
$$
 T_\eta=\varphi(q)N^{-1-2\eta}R(N)
       +O_g(q^{1/2-2\eta}\log^C q).
$$
This exhibits a power saving on the entire finer-grid discrepancy with a fixed balanced test. On the surviving line the same equivalence $T_\eta=o(q^{1-2\eta})\iff R(N)=o(N)$ holds, including along a moving $\eta=c/\log(2q)$. A target with no prime pair would have actual mass $O_g(\sqrt N\log^{O(1)}N)$ by counting proper prime powers. Its residual would be $-N\mathfrak S(N)\int g^2+o(N)$. The obstruction is present inside the product cutoff, after subtracting the model and even for a separable smooth test. A Voronoi or Kloosterman treatment that saves on this test must estimate the fixed-shift convolution itself. The original norm $B_q$ uses its own Mellin kernel. Transferring a norm estimate to this test would require controlling the change of kernel.

## 4. Comparing what the three bounds would buy

| Route | [P] Required margin | [I] Analytic accessibility |
|---|---|---|
| B-015, $D_{1,1.4}$ | Given [U] supply $T\ge .031SN/L^2$, a bound $B\le(.031-\delta)SN/L^2$ gives $G=(T-B)/2\ge(\delta/2)SN/L^2$. Strict inequality without a fixed gap gives positivity. | Product distribution gives a quantitative loss bound for the unsigned narrowing step. The narrower set gets the smaller remaining margin in §1. Genuine Möbius bias still needs an independent estimate. |
| B-005, capped at $\beta=1/5$ | $H_J\le(0.577730176\ldots-\epsilon)NV_N$ gives $2G_R\ge(\epsilon-o(1))NV_N$. Dividing by $L$ gives ordered count at least $(5e^{-\gamma}\epsilon/2-o(1))SN/L^2$. | The unsigned baseline is available at BV level. The new cutoff increases it, but the capped signed difference is exactly twice the rough prime mass. |
| B-004, original moving-line norm | $B_q(c/\log(2q))/\varphi^*(q)\to0$ uniformly on primitive conductors implies $G_\Lambda(N)=N\mathfrak S(N)+o(N)$ under the detector's hypotheses. | Strongest stated output. It requires vanishing relative error in an absolute norm. Even a balanced signed test at a single sparse conductor retains a full single-shift discrepancy. |

[I] B-015 and B-005 tie at the level of a positive lower bound given a fixed signed gap. Their thresholds use different statistics, units, and supply hypotheses. The numbers .031 and .577730 do not order the difficulty of proving their signed estimates. B-015 has a directly estimable loss when narrowing. The B-005 scan measures a capped margin of 0.30183 on its upper half at 0.201. The moving-line criterion asks for the full asymptotic. A synthetic prime-free plus model has $B=T$ and $H_J=S_z$, so its signed gaps vanish for both sieve routes. [U] No uniform genuine signed gap, pointwise ratios saving, or binary Goldbach proof emerges here.
