/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandLocalRank
import Mathlib.Algebra.Field.ZMod

/-!
# Asymmetric-band local-rank boundary checks

The actual `Y₀` substitution has a `TE` term of contact order three at derivative order two.
It is removed at multiplicity three and retained at multiplicity four. This detects confusion
between the error weight `d` and the shifted counting denominator `d+1`.
-/

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

private noncomputable def te : LocalVariable 2 →₀ ℕ :=
  Finsupp.single (localT 2) 1 + Finsupp.single (localE 2) 1

/-- The exact contact boundary is excluded from the actual local map. -/
example : MvPolynomial.coeff te
    (localConstraintAt 3 (0 : ℚ) 0 (X (some (0 : Fin 3)))) = 0 := by
  rw [localConstraintAt, LinearMap.comp_apply, projectLowContact, coeff_filterLocalMonomials]
  norm_num [localContactOrder, te, Finsupp.weight_single]

/-- The same `TE` coefficient is retained one step above the boundary. -/
example : MvPolynomial.coeff te
    (localConstraintAt 4 (0 : ℚ) 0 (X (some (0 : Fin 3)))) = 1 := by
  rw [localConstraintAt, LinearMap.comp_apply, projectLowContact, coeff_filterLocalMonomials]
  norm_num [localContactOrder, te, Finsupp.weight_single]
  simp [localCorrection, Fin.sum_univ_two, X, monomial_pow, localT, localE, localAux, localY]
  have h₁ : (Finsupp.single (some (some (0 : Fin 2))) 1 : LocalVariable 2 →₀ ℕ) ≠
      Finsupp.single (some none) 1 := by
    intro h
    have h' := congrArg (fun f : LocalVariable 2 →₀ ℕ ↦ f (some none)) h
    simp at h'
  have h₂ : (Finsupp.single none 1 + Finsupp.single none 1 +
      Finsupp.single (some (some (1 : Fin 2))) 1 : LocalVariable 2 →₀ ℕ) ≠
      Finsupp.single none 1 + Finsupp.single (some none) 1 := by
    intro h
    have h' := congrArg (fun f : LocalVariable 2 →₀ ℕ ↦ f (some none)) h
    simp at h'
  simp [h₁, h₂]

/-- Small characteristic and `d ≥ D` cause no problem for this local support argument. -/
example (center received : ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.range
      (asymmetricBandLocalConstraint (d := 2) (m := 4) (W := 3)
        (Cmin := 1) (Cmax := 2) (L := 5) (by decide : 0 < 1) center received)) ≤
      asymmetricBandLocalBudget 2 4 3 ⌈(5 : ℝ) / 1 - 1⌉₊ := by
  simpa using finrank_asymmetricBandLocalConstraint_le (d := 2) (D := 1)
    (m := 4) (W := 3) (Cmin := 1) (Cmax := 2) (L := 5)
    (by decide) (by decide) center received

end ReedSolomon.HiddenDerivative
