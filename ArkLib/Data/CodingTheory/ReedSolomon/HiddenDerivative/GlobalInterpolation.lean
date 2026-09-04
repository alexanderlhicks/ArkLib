/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.LocalConstraintMap

/-!
# A nonzero global hidden-derivative interpolant

This file extracts a nonzero polynomial satisfying every local interpolation constraint from a
strict comparison between the exact interpolation dimension and the rank of the global constraint
map.  The rank comparison is an explicit premise: its eventual proof is the separate local-rank
and uniform-parameter analysis.

The global constraint map has finite-dimensional domain but an infinite-dimensional polynomial
codomain.  Accordingly, the proof uses rank-nullity with the map's finite-dimensional range and
does not assume that the codomain is finite-dimensional.
-/

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F]
variable {D A d m M W : ℕ}
variable {ι : Type*} [Fintype ι]

/-- A strict rank-versus-dimension comparison gives a nonzero exact coefficient vector in the
kernel of the global constraint map.  This coefficient-level form is the direct rank-nullity
interface for later checked linear solvers. -/
theorem exists_nonzero_global_interpolation_coefficients_of_rank_lt
    (hdD : d < D) (centers received : ι → F)
    (hrank : Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ v : ExactInterpolationCoefficients F D A d m M W hdD,
      v ≠ 0 ∧
        globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received v = 0 := by
  let Φ := globalExactCoefficientConstraintMap
    (D := D) (A := A) (m := m) (M := M) (W := W) hdD centers received
  change Module.finrank F Φ.range <
    Module.finrank F (exactInterpolationSpace F D A d m M W hdD) at hrank
  have hcoeff : Module.finrank F
      (ExactInterpolationCoefficients F D A d m M W hdD) =
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD) :=
    LinearEquiv.finrank_eq (exactInterpolationPolynomial hdD)
  have hnull := LinearMap.finrank_range_add_finrank_ker Φ
  have hkerpos : 0 < Module.finrank F Φ.ker := by
    rw [← hcoeff] at hrank
    omega
  have hker : Φ.ker ≠ ⊥ := by
    intro h
    rw [h] at hkerpos
    simp at hkerpos
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, LinearMap.mem_ker.mp hvker⟩

/-- If the exact global constraint rank is strictly smaller than the exact interpolation
dimension, there is a nonzero polynomial in the exact interpolation space satisfying every local
constraint.  This is the conditional `I5` global interpolation theorem; proving the rank premise
is deliberately left to `I4` and the uniform interpolation certificate. -/
theorem exists_nonzero_global_interpolant_of_rank_lt
    (hdD : d < D) (centers received : ι → F)
    (hrank : Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨v, hv0, hvker⟩ :=
    exists_nonzero_global_interpolation_coefficients_of_rank_lt hdD centers received hrank
  let Qs : exactInterpolationSpace F D A d m M W hdD :=
    exactInterpolationPolynomial hdD v
  refine ⟨Qs, ?_, Qs.property, ?_⟩
  · intro hQ
    have hQs : Qs = 0 := by
      apply Subtype.ext
      simpa using hQ
    apply hv0
    have hrepr := congrArg
      (exactInterpolationRepr (F := F) (D := D) (A := A) (d := d) (m := m)
        (M := M) (W := W) hdD) hQs
    simpa [Qs] using hrepr
  · intro i
    have hi := congrFun hvker i
    simpa [SatisfiesLocalConstraints, exactCoefficientLocalConstraintAt,
      exactInterpolationCoefficientEvaluator, Qs] using hi

/-- Convenience form for rank certificates: an explicit upper bound on the exact global rank,
together with strict inequality from that bound to the exact interpolation dimension, produces
the global interpolant. -/
theorem exists_nonzero_global_interpolant_of_rank_le
    (hdD : d < D) (centers received : ι → F) (rankBound : ℕ)
    (hrank : Module.finrank F
        (globalExactCoefficientConstraintMap (D := D) (A := A) (m := m) (M := M) (W := W)
          hdD centers received).range ≤ rankBound)
    (hdim : rankBound <
      Module.finrank F (exactInterpolationSpace F D A d m M W hdD)) :
    ∃ Q : DifferentialPolynomial F d,
      Q ≠ 0 ∧
        Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  exact exists_nonzero_global_interpolant_of_rank_lt hdD centers received (hrank.trans_lt hdim)

end ReedSolomon.HiddenDerivative
