/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ExtensionRootCount

/-!
# Root counting with the first-separant degree saving

Differentiating a jet variable removes weight at least `D-d`. This saving persists for the
separant of every equation along the singular chain, since the equation's weighted degree never
increases. Consequently the exceptional-point budget is `weightedDegree Q - (D-d)`, not the
original weighted degree. Natural subtraction covers a zero or negative untruncated budget.

The resulting extension bound keeps the conservative prefactor `2*(d+1)*t²`; it does not assert
the manuscript's sharper total-jet-degree prefactor or an executable enumerator.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z.,
  *Reed--Solomon List Decoding up to Capacity at Every Rate*][DKTZ26], Section 7,
  source revision `9e4d6488ead94be47cca69e5be915b5667143b66`.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F] [Finite F] {d D : ℕ}

/-- Division-free root bound using the reduced first-separant budget at every recursive leaf. -/
theorem boundedSolution_sub_mul_le_of_separant_budget
    (Q : DifferentialPolynomial F d) (H t : ℕ)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) :
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
      Nat.card F * ((d + 1) * t ^ 2 * Nat.card F ^ d) := by
  let := Fintype.ofFinite (BoundedSolution Q D)
  have hRegular : RegularBranchBudget Q D (Nat.card F - H)
      (Nat.card F * t * Nat.card F ^ d) := by
    intro current s hreach hactive hcurrent regular hregular
    apply boundedSolution_counting_pow_le current s D H t regular hregular
    · intro solution _
      have hweight := differentialWeightedDegree_le_of_reflTransGen_singularStep (D := D) hreach
      have hs : s.val ≤ d := Nat.le_of_lt_succ s.isLt
      have hbudget : differentialWeightedDegree D current - (D - s.val) ≤ H := by omega
      exact (natDegree_differentialSpecialization_separant_le_sub current s solution.polynomial
        (Polynomial.natDegree_le_of_degree_le solution.degree_le)).trans hbudget
    · intro point
      exact (polynomialJet_injOn_regularWitness current s
        (isHighestActiveJet_of_highestActiveJet_eq_some hactive) hcurrent.1 point).mono
          (fun _ hmem ↦ hmem.2)
    · exact (jetDegree_le_of_reflTransGen_singularStep hreach s).trans (hDegree s)
  have hcount := boundedSolution_recursive_counting_of_jetDegree_le Q hQ hchar
    (Nat.card F - H) (Nat.card F * t * Nat.card F ^ d) t Finset.univ hDegree hRegular
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcount
  calc
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
        ((d + 1) * t) * (Nat.card F * t * Nat.card F ^ d) := hcount
    _ = _ := by ring

/-- Extension witnesses preserve the reduced separant budget and count only base-field roots. -/
theorem boundedSolution_extension_sub_mul_le_of_separant_budget
    (Q : DifferentialPolynomial F d) (e H t : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) :
    (Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D) ≤
      Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d)) := by
  let : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  let : NeZero e := ⟨he.ne'⟩
  let E := FiniteField.Extension F (ringChar F) e
  let Qₑ : DifferentialPolynomial E d := MvPolynomial.map (algebraMap F E) Q
  have hcardE : Nat.card E = Nat.card F ^ e :=
    FiniteField.natCard_extension F (ringChar F) e
  have hQₑ : Qₑ ≠ 0 := by
    intro hzero
    apply hQ
    apply MvPolynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    simpa [Qₑ] using hzero
  have hcharₑ : IsBelowCharacteristic D Qₑ :=
    (isBelowCharacteristic_map_iff Q D).mpr hchar
  have hWeightₑ : differentialWeightedDegree D Qₑ - (D - d) ≤ H := by
    simpa only [Qₑ, differentialWeightedDegree_map_eq
      (algebraMap F E) (algebraMap F E).injective Q] using hWeight
  have hDegreeₑ : ∀ s, jetDegree Qₑ s ≤ t := by
    intro s
    simpa only [Qₑ, jetDegree_map_eq (algebraMap F E) (algebraMap F E).injective Q s]
      using hDegree s
  have hcount := boundedSolution_sub_mul_le_of_separant_budget Qₑ H t hQₑ hcharₑ
    hWeightₑ hDegreeₑ
  have hDescent : Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution Qₑ D) :=
    BoundedSolution.natCard_le_extension Q D
  calc
    (Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D) ≤
        (Nat.card F ^ e - H) * Nat.card (BoundedSolution Qₑ D) :=
      Nat.mul_le_mul_left _ hDescent
    _ ≤ _ := by simpa only [hcardE, pow_mul] using hcount

/-- Half the witness field suffices using the separant budget, rather than the original degree.
Taking `e=1` or `e=2` gives the base-field or quadratic-extension exponent, respectively. -/
theorem natCard_boundedSolution_le_extension_pow_of_separant_budget
    (Q : DifferentialPolynomial F d) (e H t : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤
      2 * (d + 1) * t ^ 2 * Nat.card F ^ (e * d) := by
  have hcount := boundedSolution_extension_sub_mul_le_of_separant_budget
    Q e H t he hQ hchar hWeight hDegree
  have hS : 0 < Nat.card F ^ e := pow_pos Nat.card_pos e
  have hhalf : Nat.card F ^ e ≤ 2 * (Nat.card F ^ e - H) := by omega
  apply Nat.le_of_mul_le_mul_left ?_ hS
  calc
    Nat.card F ^ e * Nat.card (BoundedSolution Q D) ≤
        (2 * (Nat.card F ^ e - H)) * Nat.card (BoundedSolution Q D) :=
      Nat.mul_le_mul_right _ hhalf
    _ = 2 * ((Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D)) := by ring
    _ ≤ 2 * (Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d))) :=
      Nat.mul_le_mul_left 2 hcount
    _ = _ := by ring

/-- Strict interpolation degree `L` gives exactly the manuscript's budget `max(0,L-K+d)`
with `K=D+1`. The field-size condition is not weakened to the larger original degree budget. -/
theorem natCard_boundedSolution_le_extension_pow_of_interpolation_degree
    (Q : DifferentialPolynomial F d) (e L t : ℕ) (he : 0 < e) (hdD : d ≤ D)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q < L)
    (hDegree : ∀ s, jetDegree Q s ≤ t)
    (hlarge : 2 * (L + d - (D + 1)) ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤
      2 * (d + 1) * t ^ 2 * Nat.card F ^ (e * d) := by
  apply natCard_boundedSolution_le_extension_pow_of_separant_budget
    Q e (L + d - (D + 1)) t he hQ hchar ?_ hDegree hlarge
  omega

end
end ReedSolomon.HiddenDerivative
