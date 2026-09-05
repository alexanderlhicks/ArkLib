# All-rate RS refinements: code handoff

Research work in progress for code review.
This is a code branch on top of `075c65576b53c04e54a8c59cdf7c466cc9ac157f`, not a claim
that the complete unpublished manuscript or its decoder runtime has been verified.

Branch: `review/all-rate-rs-refinements`.

## What is implemented

| Layer | New result | Status |
|---|---|---|
| Root counting | Exact good-witness denominator; division-free eighth-budget count | Proved |
| Band list adapter | Integer-rounded `32/7` coefficient with the eighth-budget premise | Proved |
| All-rate frontend | Default prime-field list bound with `floor(32(d+1)m²q^(2d)/7)` | Proved |
| Canonical certificate | Exact-list and `Code.Lambda` consequences; convenient prefactor `5(d+1)m²` | Proved |
| Finite sorting bridge | Weighted sum preserved, degree equals maximum, factorial fiber count | Proved |
| Finite mass adapter | Maximum-event mass implies normalized band cardinality | Proved |
| Exact coordinate tails | Guarded residual-simplex count, product ratio, negative correlation | Proved |
| Maximum band mass | Second-moment lower bound minus an upper union bound | Proved |
| Exponential tail bounds | Finite lower correction and upper denominator `W+r` | Proved |
| Sharper rank | Coefficient `10/3` conditional on band coefficient `13/20` | Proved with explicit premise |
| Candidate endpoint | Order `ceil(exp((23/4)/δ))` satisfies scalar threshold `540` | Proved |
| Sharper dimension | Cubic denominator `140` instead of `162`, with finite ceiling reserve | Proved |
| Tunable endpoint | Uniform `c² exp(c/2)` lower bound for every `c≥4` | Proved |
| Further candidate endpoint | Order `ceil(exp((11/2)/δ))` exceeds the new threshold `1400/3` | Proved |
| Interpolation adapter | Actual nonzero band polynomial from sharper mass and endpoint | Proved with explicit premises |
| Uniform `13/20` mass | Maximum-coordinate tail estimates at the prescribed parameters | Still open in Lean |
| Full smaller-order construction/list capstone | Parameter assembly plus the missing tail estimate | Not claimed |

No new `sorry`, project axiom, native-computation proof, or runtime claim is introduced.
The original `6.76` construction and larger-field theorem are preserved.

## Review the unconditional improvement first

1. In [SeparantRootCount](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/SeparantRootCount.lean),
   the division-free inequality `(S-H)*N ≤ S*P` now has an exact natural-division corollary
   when `H<S`. Under `8H≤S`, it also gives `7N≤8P`.
2. In [BandConstruction](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/BandConstruction.lean),
   `agreeingPolynomials_encard_le_div_seven_of_band_certificate` carries that bound through the
   original message-degree and agreement frontend.
3. In [StrongBand](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/StrongBand.lean),
   `strong_band_pointwise_div_seven` discharges the budget from the original prescribed parameters.
   `strong_band_certificate_div_seven` includes the exact list, canonical relative-radius bound,
   and infeasible-threshold case. `strong_band_certificate_five` supplies a simpler gap-only factor.

The original block hypothesis gives `8mA≤q²`, and `d<K` gives
`max(0,mA+d-K)≤mA`. Thus the default quadratic-extension branch already has the required
eighth-budget condition. The original degree-one larger-field branch has only a half-budget
condition: its old prefactor is intentionally not changed.

The natural floor applies to the whole product. It is not moved inside a gap-only factor.

## Then review the new finite counting argument

[SimplexPartitionCounting](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexPartitionCounting.lean)
sorts a tuple `u` into descending coordinates `x`, extends `x` by zero, and sets
`c_i=x_i-x_(i+1)`. It proves:

```text
sum (i+1)*c_i = sum u_i
sum c_i       = max u_i
(c, sorting permutation) determines u
```

Consequently, a simplex event with `Cmin≤max u≤Cmax` has cardinality at most
`card(asymmetricBandTuples)*r!`. This avoids the old coordinate-floor loss. The zero-dimensional
case is included, and no equal-fiber-size assumption is made.

The last theorem converts any finite maximum-event mass certificate into the precise
`mass * W^r/(r!)²` band lower bound consumed by the rank calculation.

[SharperBandNormalizedRank](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/SharperBandNormalizedRank.lean)
reuses the existing generic estimates and proves the improved conditional rank coefficient:

```text
(9/8)*(20/13)*(101/100)*(19/10) < 10/3
162*(10/3) = 540
```

[SharperBandEndpoint](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SharperBandEndpoint.lean)
reuses generic endpoint monotonicity and proves the new low-/high-rate endpoint and multiplicity
bounds at `23/4=5.75`. The crucial numeric margin is certified by rational exponential partial sums,
not floating-point computation.

## Further improvement: count more of each band fiber

[AsymmetricBandDimensionBound](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/AsymmetricBandDimensionBound.lean)
now exposes the simplex fraction `θ` and upper-cutoff slope `β`. The sufficient rounding condition is

```text
2 ≤ (1-β-θ)*g*m
dimension ≥ B*D*m³*g³*θ³/6.
```

For `β=13/20`, take `θ=17499/50000=0.34998`, leaving `gm/50000` for both ceilings.
The existing hypotheses `d≥1000` and `gm≥100(d+1)` imply `gm≥100000`, so this gives

```text
dimension ≥ B*D*m³*g³/140
140*(10/3) = 1400/3.
```

This is a `81/70 ≈ 1.157` factor improvement in the dimension lower bound under the prescribed
large-order hypotheses. The old `/162` theorem and its smaller multiplicity domain are preserved.
There is no band-mass premise in the dimension improvement itself.

[TunableBandEndpoint](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TunableBandEndpoint.lean)
proves both rate regimes and the multiplicity bound with a variable `c≥4`, then specializes to
`c=11/2=5.5`. Its high-rate endpoint is `473.1896… > 1400/3`, certified by a rational Taylor sum.
[SharperBandComparison](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/SharperBandComparison.lean)
connects the improved constants to the exact integer dimension comparison and a genuine nonzero
band interpolant, conditional on `13/20` band mass and the endpoint inequality.

**The full `5.5` list-decoding bound is not yet proved.** The available harmonic estimate
`H_r≤log r+3/5` suggests stronger lower-tail margins than the earlier `+1` estimate. With finite
errors bounded by `1/100`, the new candidate gives

```text
log μ ≥ (3/5)*(11/2) - 3/5 - 1/100 = 269/100
log ν ≤ -1/2 - (3/20)*(11/2) + 1/100 = -263/200
μ ≥ 14,  ν ≤ 27/100
14/15 - 27/100 = 199/300 > 13/20.
```

The rational exponential margins and the finite mass adapter for these two tail bounds are proved.
The uniform substitution of the actual rounded parameters into those analytic bounds is still open;
neither floating-point experiments nor the scalar endpoint theorem discharge that obligation.
See [the finite argument](docs/research/all-rate-partition-count.md#5-a-sharper-dimension-and-a-further-candidate)
for the derivation and the precise proof boundary.

## The remaining proof target is concrete

The complete finite derivation, including rounding errors and every numerical margin, is in
[the partition-count note](docs/research/all-rate-partition-count.md). Its Lean proof status is
marked separately from the mathematical argument.

For a uniform ordinary simplex `U={u in N^r : sum u≤W}`, shifting coordinates gives

```text
p(t) = Pr[u_1≥t] = choose(W-t+r,r) / choose(W+r,r)     (0≤t≤W)
p(2t) ≤ p(t)^2
μ = r*p(Cmin)
ν = r*p(Cmax+1)
Pr[Cmin≤max u≤Cmax] ≥ μ/(1+μ) - ν.
```

The review's finite analytic argument targets `μ>11` and `ν<13/50`, giving
`11/12-13/50=197/300>13/20`. At `d=ceil(exp(5.75/δ))`, it uses
`gH/(1+g/2)≥5.75`, `1/2≤H_(d-1)-log(d-1)≤1`, and explicitly bounded rounding errors below `1/100`.
The finite identities, negative correlation, second-moment and union bounds are now proved in
[SimplexCoordinateTail](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexCoordinateTail.lean)
and [SimplexMaximumTail](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexMaximumTail.lean).
In particular, `asymmetricBand_card_lower_of_tail_margins` proves the `13/20` band count from
the two explicit numerical premises `11≤μ` and `ν≤13/50`.
The rank adapter `SharperBand.finrank_asymmetricBandLocalConstraint_le_normalized_of_tail_margins`
then gives the `10/3` bound for the actual local constraint without a separate band-count premise.

[SimplexTailBounds](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexTailBounds.lean)
also proves the discrete exponential estimates

```text
exp(-r*z/(1-z)) ≤ p(t),  z=t/(W+1),  t≤W
p(t) ≤ exp(-r*t/(W+r)),  r>0.
```

The lower exponent equals `-r*z-r*z²/(1-z)`, so the finite correction is retained.
The missing uniform step is now to discharge the numerical tail premises for the actual rounded
all-rate parameters. Those uniform estimates are **not yet a Lean theorem**. No axiom or
fabricated completed capstone stands in for them. The scalar exponential margins are checked.

Treat this as progress over the pinned implementation, not a settled priority claim or a review
of the complete manuscript.

## Reproduce

With the pinned Lean/dependency setup available:

```bash
./scripts/check-all-rate-refinements.sh
```

This builds the relevant modules, runs `scripts/AllRateRefinementAudit.lean` under `--trust=0`,
rejects principal-theorem axioms other than `propext`, `Classical.choice`, and `Quot.sound`,
and runs exact integer/rational experiments on 65 small simplexes and 2275 bands, plus 6084
threshold pairs for the product and correlation formulas (including dimension zero), and 60
dimension-rounding cases including the exact multiplicity threshold.
The tests illustrate and regression-check the counting identities; they do not prove a uniform
asymptotic theorem. The script does not upload artifacts or run a decoder benchmark.

Before integration, also run:

```bash
./scripts/validate.sh --axioms
```

The focused audit complements, rather than replaces, the repository-wide axiom sweep and style,
runtime, import, and documentation gates.

The audit now covers 45 principal declarations, including the new dimension, tunable endpoint,
interpolation, and tail-margin theorems. Its Lean canaries include an explicit counterexample to
using the limiting `7/20` simplex fraction without reserving room for ceilings. All new scalar
certificates also have independent exact-rational Taylor-sum checks.

## Optional offline transport

An incremental Git bundle can be fetched into a repository containing the pinned base:

```bash
git bundle verify /path/to/all-rate-rs-refinements.bundle
git fetch /path/to/all-rate-rs-refinements.bundle \
  review/all-rate-rs-refinements:review/all-rate-rs-refinements
git switch review/all-rate-rs-refinements
```

The bundle contains the committed code,
audit, tests, and this handoff, not the local research scratch files or the user's other work.

The proofs and review were developed with Codex; adaptations preserve Quang's original file credit.
