/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.GlobalMultiplicity
import Mathlib.Algebra.Field.ZMod

/-!
# Canaries for global polynomial multiplicity

The examples use the nonconsecutive points `1` and `4` in `ZMod 7`. They protect local
injectivity, the strict degree inequality, and the satisfiable zero boundaries of the
`WithBot`-valued degree theorem.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

private def nonconsecutivePoints : Fin 2 ↪ ZMod 7 where
  toFun i := if i = 0 then 1 else 4
  inj' := by decide

/-- The natural-degree theorem specializes to two nonconsecutive double roots. Supplying
`hpoints` and `hdegree` by name pins the injectivity and strictness boundaries of the API. -/
example {W : (ZMod 7)[X]}
    (hdiv : ∀ i : Fin 2, (X - C (nonconsecutivePoints i)) ^ 2 ∣ W)
    (hdegree : W.natDegree < 4) :
    W = 0 := by
  exact Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    (points := nonconsecutivePoints) (indices := Finset.univ)
    (multiplicity := 2) (requiredPoints := 2)
    (hpoints := nonconsecutivePoints.injective.injOn) (hcard := by simp)
    (hdiv := by simpa using hdiv) (hdegree := by simpa using hdegree)

private def exactBoundaryPolynomial : (ZMod 7)[X] :=
  (X - C 1) ^ 2 * (X - C 4) ^ 2

/-- Strictness is necessary: the product of the two prescribed squared factors is nonzero and
has degree exactly the total multiplicity. -/
example :
    exactBoundaryPolynomial ≠ 0 ∧
      exactBoundaryPolynomial.natDegree = 4 ∧
      ∀ i : Fin 2,
        (X - C (nonconsecutivePoints i)) ^ 2 ∣ exactBoundaryPolynomial := by
  constructor
  · exact (((monic_X_sub_C (1 : ZMod 7)).pow 2).mul
      ((monic_X_sub_C (4 : ZMod 7)).pow 2)).ne_zero
  constructor
  · rw [exactBoundaryPolynomial,
      natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero 1))
        (pow_ne_zero 2 (X_sub_C_ne_zero 4)),
      natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C]
  · intro i
    fin_cases i <;> simp [nonconsecutivePoints, exactBoundaryPolynomial]

private def collidingPoints (_i : Fin 2) : ZMod 7 := 1

private def collisionPolynomial : (ZMod 7)[X] :=
  (X - C 1) ^ 2

/-- Injectivity is necessary: counting the same double root twice would incorrectly claim total
multiplicity four for this nonzero quadratic. -/
example :
    ¬Set.InjOn collidingPoints (Finset.univ : Finset (Fin 2)) ∧
      (∀ i : Fin 2, (X - C (collidingPoints i)) ^ 2 ∣ collisionPolynomial) ∧
      collisionPolynomial.natDegree < 4 ∧ collisionPolynomial ≠ 0 := by
  constructor
  · intro hinjective
    have hzero_one : (0 : Fin 2) = 1 := hinjective (by simp) (by simp) rfl
    simp at hzero_one
  constructor
  · intro i
    simp [collidingPoints, collisionPolynomial]
  constructor
  · rw [collisionPolynomial, natDegree_pow, natDegree_X_sub_C]
    omega
  · exact ((monic_X_sub_C (1 : ZMod 7)).pow 2).ne_zero

/-- Empty agreement data and zero required points remain satisfiable for the zero polynomial when
the `WithBot`-valued degree formulation is used. -/
example {F : Type*} [Field F] (points : Empty → F) :
    (0 : F[X]) = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      points ∅ 5 0
  · simp
  · simp
  · simp
  · simp

/-- Zero multiplicity is likewise a valid boundary for the zero polynomial in the degree
formulation, even with a positive required-point count. -/
example : (0 : (ZMod 7)[X]) = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      nonconsecutivePoints Finset.univ 0 2
  · exact nonconsecutivePoints.injective.injOn
  · simp
  · simp
  · simp

end

end ReedSolomon.HiddenDerivative
