/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.DifferentialEquation
import ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-!
# Global multiplicity for hidden-derivative specialization

This file connects the generic distinct-root multiplicity bound to differential specialization.
If a specialization has contact of order `multiplicity` at at least `requiredPoints` distinct
evaluation points and its natural degree is strictly below `multiplicity * requiredPoints`, then
it vanishes identically.

The local-contact and specialization-degree layers supply the two polynomial hypotheses in the
final interpolation theorem. Keeping their composition separate here leaves the root-counting
argument independent of the definitions used to obtain local contact and the degree budget.
-/

namespace ReedSolomon.HiddenDerivative

open Polynomial

/-- A differential specialization vanishes when it has enough distinct roots of uniform
multiplicity for its strict natural-degree budget. The evaluation map need only be injective on
the selected agreement indices, whose actual cardinality may exceed `requiredPoints`. -/
theorem differentialSpecialization_eq_zero_of_global_multiplicity
    {ι F : Type*} [Field F] {d : ℕ} (points : ι → F) (indices : Finset ι)
    (multiplicity requiredPoints : ℕ) (Q : DifferentialPolynomial F d) (P : F[X])
    (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : requiredPoints ≤ indices.card)
    (hcontact : ∀ i ∈ indices,
      (X - C (points i)) ^ multiplicity ∣ differentialSpecialization Q P)
    (hdegree : (differentialSpecialization Q P).natDegree <
      multiplicity * requiredPoints) :
    differentialSpecialization Q P = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    points indices multiplicity requiredPoints hpoints hcard hcontact hdegree

end ReedSolomon.HiddenDerivative
