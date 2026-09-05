# Finite argument for the sharper band count

This note records the finite argument behind the verified `5.5` all-rate refinement. The sorting/permutation bridge, exact tails, negative correlation, second-moment bound, uniform rounded-parameter estimates, and final construction/list theorem are now proved. Section 3 preserves the historical `5.75` derivation; Section 5 gives the stronger completed route. The capstone is [RefinedBand](../../ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/RefinedBand.lean).

This is a verified refinement of the pinned implementation, not a review of the complete manuscript.
No novelty or runtime claim is made.

## 1 Sort an ordinary simplex instead of dividing coordinates

Put `r=d−1` and

\[
U=\{u\in\mathbb N^r:\sum_i u_i\le W\},\qquad |U|=\binom{W+r}{r}.
\]

For `u∈U`, sort its coordinates as `x₁≥…≥xᵣ≥0`, set `xᵣ₊₁=0`, and define `cⱼ=xⱼ−xⱼ₊₁`. Telescoping gives

\[
\sum_{j=1}^r j c_j=\sum_i u_i\le W,
\qquad\sum_{j=1}^r c_j=x_1=\max_i u_i.
\]

Consequently, `Cmin≤max(u)≤Cmax` maps into exactly the higher-jet band already used by ArkLib. Each fiber has at most `r!` members: `c` uniquely determines the sorted coordinates, and its preimages are their permutations. Repeated coordinates only decrease the fiber size.

For example, `u=(2,5,1)` sorts to `(5,2,1)` and produces `c=(3,1,1)`. Its weighted sum is `3+2+3=8=sum(u)` and its ordinary sum is `5=max(u)`.

Writing `B` for the number of band tuples, we obtain the exact finite inequality

\[
B\ge\frac{|\{u\in U:C_{\min}\le\max_i u_i\le C_{\max}\}|}{r!}.
\tag{1}
\]

There is no coordinate-floor loss. The factorial is an orbit-size bound, not a claim that all orbits have the same size. This is a partition-conjugation viewpoint; the standard correspondence and restricted generating functions are documented in [NIST DLMF §26.9](https://dlmf.nist.gov/26.9).

## 2 An exact formula and a simple uniform lower bound

Equations (2) and (3), including the necessary over-budget guard and zero-mean case, are proved in
[SimplexCoordinateTail](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexCoordinateTail.lean)
and [SimplexMaximumTail](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexMaximumTail.lean).
The inclusion-exclusion formula (4) is exact-test-checked but not yet formalized.

For `r≥1`, under the uniform distribution on `U`, for integer `0≤t≤W`,

\[
p(t):=\Pr(u_1\ge t)
=\frac{\binom{W-t+r}{r}}{\binom{W+r}{r}}
=\prod_{i=1}^r\left(1-\frac{t}{W+i}\right).
\tag{2}
\]

Set `p(t)=0` for `t>W`. For `r≥2`, shifting two distinct coordinates shows

\[
\Pr(u_1\ge t,u_2\ge t)=p(2t)\le p(t)^2.
\]

For `2t≤W`, the inequality holds factorwise by `1−2z≤(1−z)²`; otherwise its left side is zero. This is the negative correlation needed here, not an assumption of independence.

Let `Z` count coordinates at least `Cmin`, and set `μ=r p(Cmin)`, `ν=r p(Cmax+1)`. Then

\[
\mathbb E Z^2\le\mu+\mu^2,\qquad
\Pr(Z>0)\ge\frac{\mu}{1+\mu}
\]

by Cauchy–Schwarz. A union bound at the upper edge gives

\[
\Pr(C_{\min}\le\max u\le C_{\max})
\ge\frac{\mu}{1+\mu}-\nu.
\tag{3}
\]

For exact finite certificates, inclusion–exclusion also gives

\[
F(b):=|\{u\in U:\max u\le b\}|
=\sum_{\substack{0\le j\le r\\j(b+1)\le W}}
(-1)^j\binom rj\binom{W-j(b+1)+r}{r}.
\tag{4}
\]

Define `F(−1)=0`; the band event count is `F(Cmax)−F(Cmin−1)`. **The condition on each term is essential:** using truncated natural subtraction inside the binomial without excluding `j(b+1)>W` would introduce spurious terms.

## 3 Uniform finite estimates at `c₀=23/4`

[SimplexTailBounds](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexTailBounds.lean)
proves the general exponential inequalities used below. This section records the earlier
candidate argument; the completed uniform Lean estimates use the sharper route in Section 5.

Now prescribe

\[
d=\lceil e^{c_0/\delta}\rceil,\quad c_0=23/4,
\quad H=H_{d-1},\quad m=\lceil100d^2H\rceil,
\]

Here `0<δ<1/4`, `δ/3≤ρ≤1−δ`, and the remaining parameters are exactly those
of the existing construction:

\[
g=\min(1,\delta/\rho),\quad a=1+g/2,\quad
W=\lfloor adm/H\rfloor,\quad
C_{\min}=\lfloor(1-g/10)m\rfloor,\quad
C_{\max}=\lceil(1+13g/20)m\rceil.
\]

In the list-decoding application, `ρ=D/n` is the ambient degree divided by block length.
The existing slack algebra gives `aδ≤g`. Consequently

\[
x:=gH/a\ge\delta H\ge c_0.
\tag{5}
\]

Here are explicit bounds sufficient for every finite correction below:

- `d≥exp(23)>10⁸`.
- `1/2≤H−log r≤1`. The upper bound follows by integral comparison; the lower bound follows by the trapezoidal upper estimate on the integral of the convex function `1/x`: `log r≤H−(1+1/r)/2`. The `r=1` case can be checked separately.
- `H≤1+log d≤d^(1/4)` in this range. For the last inequality write `t=(log d)/4≥23/4`; the cubic partial sum of `exp(t)` is already at least `1+4t` for `t≥4`.

**Lower edge.** Put `z=Cmin/(W+1)`. Since `W+1>adm/H`,

\[
0\le z\le H/d<1,\qquad
rz\le(1-g/10)H/a=H-3x/5.
\]

This also ensures `Cmin≤W`. Using `log(1−z)≥−z−z²/(1−z)` in (2),

\[
\log\mu\ge\log r-rz-\frac{rz^2}{1-z}
> -1+\frac35c_0-\frac1{100}=\frac{61}{25}.
\tag{6}
\]

The error is bounded by `H²/[d(1−H/d)]<1/100`, using the explicit large-`d` estimates above: `H/d≤10⁻⁶` and `H²/d≤10⁻⁴` already suffice. Since `exp(61/25)>11`, we have `μ>11`.

**Upper edge.** Put `b=Cmax+1>(1+13g/20)m`. If `b>W`, then `ν=0`. Otherwise, using `W+r≤adm/H+d` and `log(1−z)≤−z`,

\[
\log\nu\le\log r-\frac{rb}{W+r}.
\]

With `y=(1+13g/20)H/a=H+3x/20`,

\[
\frac{rb}{W+r}\ge
\frac{1-1/d}{1+H/(am)}y
\ge y-y\left(\frac1d+\frac{H}{am}\right).
\]

Since `y≤2H` and `m≥100d²H`, the last error is at most `2H/d+2H²/m<1/100`. It follows that

\[
\log\nu< -\frac12-\frac3{20}c_0+\frac1{100}
=-\frac{541}{400}.
\tag{7}
\]

The rational exponential certificate `exp(541/400)>50/13` gives `ν<13/50`.

Equations (3), (6), and (7) imply

\[
\Pr(\text{band event})>
\frac{11}{12}-\frac{13}{50}
=\frac{197}{300}>\frac{13}{20}.
\]

Combining (1) with stars and bars, `binom(W+r,r)≥W^r/r!`, yields

\[
\boxed{\quad B\ge\frac{13}{20}\frac{W^{d-1}}{((d-1)!)^2}.\quad}
\tag{8}
\]

The pinned parent implementation uses `29/100` in place of `13/20`. Equation (8) is now proved
at the smaller constant `11/2` by `asymmetricBand_mass_of_simplex_parameters` and the refined
parameter assembly; see Section 5.

## 4 Feed the stronger count into the existing rank and dimension bounds

Before rounding upward, the current normalized rank proof has coefficient

\[
\frac98\cdot\frac1{\text{mass}}\cdot\frac{101}{100}\cdot\frac{19}{10}.
\]

Replacing the mass by `13/20` gives

\[
\frac98\cdot\frac{20}{13}\cdot\frac{101}{100}\cdot\frac{19}{10}
=\frac{17271}{5200}<\frac{10}{3}.
\]

Thus the local budget is at most

\[
\frac{10}{3}\frac{ga^2}{H^2}B m^3d^{-g/(2+g)}.
\]

For this first candidate, use the original cubic dimension lower bound:

\[
\dim\ge BDm^3g^3/162.
\]

The sufficient scalar condition therefore becomes

\[
d^{g/(2+g)}H^2\rho g^2/a^2>540,
\tag{9}
\]

instead of `>1215`. The original endpoint argument adapts to `c₀=23/4`; its difficult high-rate endpoint is bounded below by

\[
c_0^2e^{c_0/2}=586.0468\ldots>540.
\]

This inequality is not justified merely by decimals: `exp(23/8)>17`, proved by a rational partial exponential sum, already gives a lower bound `562.0625>540`. The full low- and high-rate endpoint proof, and the prescribed multiplicity threshold, are in [SharperBandEndpoint](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SharperBandEndpoint.lean). The conditional normalized rank proof is in [SharperBandNormalizedRank](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/SharperBandNormalizedRank.lean).

The remaining ambient and field budgets have ample room. From `n≥8m` we get `δn≥800c₀d²=4600d²`, replacing the old `5408d²`. This still gives `δn≥12`, `d<D`, and the rate interval used above. Also `gm≥100(d+1)`, `2m<q`, and `8mA≤q²` remain available. No new characteristic assumption or evaluation-set restriction is being introduced.

## 5 A sharper dimension and the completed 5.5 theorem

The original discrete dimension proof places a simplex of side `ceil(gm/3)` inside each band
fiber. The upper cutoff `Cmax=ceil((1+13g/20)m)` actually leaves almost `7gm/20` of the degree
budget. More generally, with cutoff slope `β` and simplex fraction `θ`, the two ceiling errors
fit whenever `2≤(1−β−θ)gm`. The exact staircase count then gives

\[
\dim\ge BDm^3g^3\theta^3/6.
\]

This generic statement is proved in
[AsymmetricBandDimensionBound](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/AsymmetricBandDimensionBound.lean).
Set `β=13/20` and `θ=17499/50000`. Then `1−β−θ=1/50000`, and `θ³/6>1/140`.
The existing `d≥1000`, `gm≥100(d+1)` assumptions imply the required `gm≥100000`, yielding

\[
\boxed{\dim\ge BDm^3g^3/140.}
\]

This is a fully proved improvement, independent of the uniform mass estimate. Simply
using `θ=7/20` would not absorb rounding: at `g=m=D=1`, the cutoff and simplex ceilings add to
`ceil(1.65)+ceil(0.35)=3>ceil(2)`. The general theorem exposes the reserve instead of hiding it.

With the already proved conditional rank coefficient `10/3`, the sufficient scalar threshold is
now `1400/3`, not `540`.
[TunableBandEndpoint](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TunableBandEndpoint.lean)
proves the entire endpoint comparison for variable `c≥4`, including the rounded order and both
rate regimes. At `c=11/2`, the limiting expression is `473.1896…>1400/3`, with a rational
Taylor-sum certificate. It also proves `gm≥100(d+1)` for these variable-constant parameters.

[SharperBandComparison](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/SharperBandComparison.lean)
assembles the sharper mass, dimension, and endpoint into a strict inequality of integer counts
and an actual nonzero interpolant over any field. The mass and scalar comparison are explicit
premises, and every denominator used in the strict comparison is positive.

The stronger mass estimate at this constant is now proved. In the lower-edge argument,
replace `H−log r≤1` with `H−log r≤3/5`, which is already proved by `band_harmonic_le_log` for
`r≥32`. Retaining the same `1/100` finite-error allowance gives

\[
\mu\ge \exp\left(-\tfrac35+\tfrac35\cdot\tfrac{11}{2}-\tfrac1{100}\right)
=\exp(\tfrac{269}{100}),\qquad
\nu\le\exp\left(-\tfrac12-\tfrac3{20}\cdot\tfrac{11}{2}+\tfrac1{100}\right)
=\exp(-\tfrac{263}{200}).
\]

The exponential margins `exp(269/100)>14` and `exp(263/200)>100/27` are proved. So is the
finite adapter from `μ≥14`, `ν≤27/100` to band mass `13/20`, since
`14/15−27/100=199/300>13/20`. The old margins `μ≥11`, `ν≤13/50` are not silently reused:
the upper-tail allowance has changed.

The proof works directly with exponentials, so it never takes the logarithm of a zero upper
tail. The lower threshold is proved feasible; the upper estimate includes the over-budget case.

The uniform-error proof in
[SimplexBandParameters](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexBandParameters.lean)
uses a simpler coarse estimate than the fourth-root comparison suggested above. For `t≥22`,
an exact rational Taylor certificate gives `exp(22)≥1000000`; multiplying by the quadratic
Taylor lower bound at `t−22` proves

\[
1000(t+1)^2\le e^t.
\]

Since `log d≥22` and `H≤log d+3/5`, this implies `1000H²≤d`. The prescribed multiplicity
also gives `1000H²≤m`. With `H≥1`, the lower finite correction is at most
`(1/1000)/(1−1/1000)<1/100`, and the upper correction is at most
`2H/d+2H²/m≤4/1000<1/100`. Every floor and ceiling is retained in the two exponent lemmas.

[SimplexBandMass](../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexBandMass.lean)
closes the uniform `13/20` mass theorem.
[RefinedBandParameters](../../ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/RefinedBandParameters.lean)
then discharges the ambient-rate, multiplicity, mass, and endpoint premises of the exact
integer dimension comparison. No counting hypothesis is left to the caller.

Finally,
[RefinedBand](../../ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/RefinedBand.lean)
proves the actual order-indexed construction, the bound
`floor(32(d+1)m²q^(2d)/7)`, its canonical exact-list/`Code.Lambda` certificate, and the
separate larger-field bound `8(d+1)m²q^d`. These hold uniformly for arbitrary injective
evaluation domains, all message dimensions `1≤k≤n`, and every prime `q≥n`, assuming `n≥8m`.
Oversized agreement thresholds are handled by empty lists. The existing order-zero list
regime is included in `refined_quantitative_all_rate`.

Compared with the earlier `5.75` candidate, the completed `5.5` theorem reduces the exponential
order scale by `exp(0.25/δ)`; at `δ=0.1` this is about `12.2`. Relative to the pinned `6.76`
theorem, the scale gain is `exp(1.26/δ)`, about `296,559` at that gap. These describe the
exponential parameters, ignoring ceilings; they are not decoding-speed measurements.
