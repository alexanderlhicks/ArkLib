# All-rate RS refinements: verified `5.5` milestone

The quantitative construction and list-bound milestone is proved in Lean.
This branch refines Quang Dao's implementation at
`075c65576b53c04e54a8c59cdf7c466cc9ac157f`; it does not claim to verify the complete manuscript,
an efficient decoder, or its runtime.

Branch: `review/all-rate-rs-refinements`.

## The theorem to review first

For every `0 < δ < 1/4`, define

```text
d = ceil(exp((11/2)/δ))
H = H_(d−1)
m = ceil(100*d²*H).
```

For every `n ≥ 8m`, every `1 ≤ k ≤ n`, every prime `q ≥ n`, every injective
evaluation domain `Fin n ↪ ZMod q`, and every received word, the number of polynomials
of degree less than `k` agreeing at least `A = k + ceil(δn)` times is at most

```text
floor(32*(d+1)*m²*q^(2d)/7).
```

The floor is taken after multiplying by the field power. If `A > n`, the list is empty.
There is no extra evaluation point or padding-field assumption; `q = n` is included.

Start with
[RefinedBand](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/RefinedBand.lean):

- `refined_hidden_derivative_construction`: an actual nonzero interpolant at this order
  and multiplicity, with the original ambient dimension and each jet degree at most `2m`.
- `refined_band_pointwise_div_seven`: the exact polynomial-list bound above.
- `refined_band_certificate_div_seven`: the canonical exact-list certificate, including
  `Code.Lambda` at radius `1 − k/n − δ` and the infeasible-threshold guarantee.
- `refined_band_certificate_of_large_field`: bound `8*(d+1)*m²*q^d` under the original
  larger-field condition `2*(m*A+d−K) ≤ q`, with truncated natural subtraction and
  `K = max(k, floor(δn/2))`.
- `refined_quantitative_all_rate`: the improved small-gap theorem together with the
  existing order-zero list bounds for `δ ≥ 1/4`.

The larger-field branch has only a half-field separant budget, so it retains prefactor `8`.
The default quadratic-extension branch has the stronger eighth-field budget and prefactor
`32/7`. Neither branch infers characteristic from the cardinality of an arbitrary field:
the frontend explicitly requires a prime field.

The original `6.76` interfaces are preserved. In
[RefinedBandParameters](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/RefinedBandParameters.lean),
`refinedDerivativeOrder_le_strong` and `refinedBandMultiplicity_le_strong` verify that
both the rounded order and block threshold do not increase. Ignoring negligible ceiling
effects, the derivative-order scale improves by `exp(1.26/δ)`; at `δ=0.1` this is about
`296,559`. This is a parameter improvement, not a measured decoding speedup.

## What closes the proof

| Layer | Verified contribution |
|---|---|
| Root counting | Exact good-witness denominator and the integer-rounded `32/7` bound |
| Sorting bridge | Weighted sum preserved, ordinary degree equals maximum, at most `r!` preimages |
| Finite tails | Guarded residual-simplex count, exact product, negative correlation |
| Maximum event | Second-moment lower bound minus an upper union bound |
| Uniform band mass | Coefficient `13/20` at the actual rounded `5.5` parameters |
| Local rank | Normalized coefficient `10/3` from that mass |
| Dimension | Cubic denominator `140`, with a finite reserve for both ceilings |
| Endpoint | Strict scalar bound `>1400/3` at `c=11/2` |
| Assembly | Exact integer dimension exceeds the combined local budgets |
| Frontend | Actual construction, exact lists, canonical radius, both field regimes |

### Exact finite counting

[SimplexPartitionCounting](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexPartitionCounting.lean)
sorts `u ∈ N^r` with `sum u ≤ W` into `x₁≥…≥xᵣ≥0` and takes consecutive gaps.
It proves `sum j*c_j = sum u`, `sum c_j = max u`, and an at-most-`r!` fiber bound.
Thus a maximum-coordinate event of mass `η` gives at least `η W^r/(r!)²` band tuples.
Repeated coordinates and the zero-dimensional convention are handled exactly.

[SimplexCoordinateTail](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexCoordinateTail.lean)
and
[SimplexMaximumTail](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexMaximumTail.lean)
prove, for the uniform ordinary simplex,

```text
p(t) = choose(W-t+r,r)/choose(W+r,r)   if t≤W, otherwise 0
p(s+t) ≤ p(s)*p(t)
μ = r*p(Cmin),   ν = r*p(Cmax+1)
Pr[Cmin≤max u≤Cmax] ≥ μ/(1+μ) − ν.
```

The over-budget guard is essential: truncated subtraction inside an unguarded binomial would
create spurious points. The proof uses negative correlation, not independence.

### Uniform errors, now discharged

[SimplexBandParameters](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexBandParameters.lean)
proves `1000 H² ≤ d` whenever `log d ≥ 22`, using an exact rational Taylor bound and
`H ≤ log d + 3/5`. It also uses `1/2 ≤ H−log(d−1) ≤ 3/5`.
The multiplicity gives `1000 H² ≤ m`. These bounds absorb the finite corrections:

```text
r*z²/(1−z) ≤ 1/100,  z=Cmin/(W+1)<1
2H/d + 2H²/m ≤ 4/1000 < 1/100.
```

The all-rate slack inequality gives `gH/(1+g/2) ≥ 11/2`.
[SimplexBandMass](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/SimplexBandMass.lean)
then proves

```text
μ ≥ exp(269/100) > 14
ν ≤ exp(-263/200) < 27/100
14/15 − 27/100 = 199/300 > 13/20.
```

There is no logarithm of a potentially zero upper-tail probability. The upper exponential
estimate includes thresholds exceeding the whole budget. The lower threshold is proved
feasible, rather than assumed.

### Rank, dimension, and strict separation

The sharper rank coefficient follows from
`(9/8)*(20/13)*(101/100)*(19/10) = 17271/5200 < 10/3`.

The dimension argument uses upper-cutoff slope `β=13/20` and simplex fraction
`θ=17499/50000`, leaving `gm/50000≥2` for both ceilings. Since `θ³/6>1/140`,

```text
dimension ≥ B*D*m³*g³/140.
```

Taking the limiting fraction `7/20` without a reserve is unsafe; the audit contains a concrete
counterexample. No real-valued dimension lower bound is treated as an attained dimension.

[TunableBandEndpoint](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/TunableBandEndpoint.lean)
proves the endpoint lower bound `c² exp(c/2)` in both rate regimes for every `c≥4`.
At `c=11/2`, an exact rational Taylor certificate gives
`c² exp(c/2)>1400/3=140*(10/3)`.
[SharperBandComparison](ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/SharperBandComparison.lean)
turns these inequalities into strict separation of the actual integer counts.
The refined parameter assembly discharges all its premises.

See [the derivation](docs/research/all-rate-partition-count.md) for the progression from the
earlier `5.75` candidate to the completed `5.5` result.

## Reproduce and audit

With the pinned Lean/dependency setup:

```bash
./scripts/check-all-rate-refinements.sh
./scripts/validate.sh --axioms
```

The focused script builds the capstones, checks 62 principal declarations under `--trust=0`,
and rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`.
Its Lean canaries include the explicit `δ=0.1` order, the quarter-gap boundary, and the
full-length `q=n` canonical bound.

Exact integer/rational experiments check 65 simplexes, 27,118 points, 2,275 bands, 6,084
threshold pairs, 60 dimension-rounding cases, and the rational exponential margins.
These finite examples illustrate the proofs; the uniform theorem is established by Lean,
not by the experiments. The scripts do not upload artifacts or run a decoder benchmark.

The repository-wide validator additionally checks the warning budget, source policy, runtime
regressions, imports, documentation, and axiom-sweep fixtures. The branch introduces no
`sorry`, project axiom, native-computation proof, or claim to efficient decoding.

This is an improvement over the pinned implementation, not a settled literature-priority claim.
The separate public zero-padding observation means qualitative all-rate coverage itself should
not be presented as our novelty. The contribution here is the verified quantitative refinement.

The proofs and review were developed with Codex; adaptations preserve Quang's original file credit.
