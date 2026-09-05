/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.StrongBand
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandNormalizedRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SharperBandEndpoint
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexPartitionCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexMaximumTail
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexTailBounds
import Lean.Util.CollectAxioms

/-!
# Focused all-rate refinement audit

Run with `lake env lean --trust=0 scripts/AllRateRefinementAudit.lean` after building its imports.
Missing declarations and any axiom beyond the accepted logical baseline fail this command.
The repository-wide axiom sweep remains a separate integration gate.

This audits the stronger root-count frontend and the proved pieces of the sharper band route.
It deliberately does not advertise an unconditional `5.75` all-rate theorem.
-/

open ReedSolomon.HiddenDerivative ReedSolomon.AllRateListDecoding
open scoped BigOperators

/-- The motivating tuple lands in the exact weight-eight, degree-five band. -/
example : partitionGaps ![2, 5, 1] ∈ asymmetricBandTuples 4 8 5 5 := by
  exact partitionGaps_mem_band (d := 4) (W := 8) (Cmin := 5) (Cmax := 5)
    ⟨![2, 5, 1], by decide⟩ (by decide) (by decide)

/-- The empty-tuple convention is covered by the same theorem. -/
example : ∑ i : Fin 0, partitionGaps ![] i = 0 := by simp

/-- Positive natural division rounds downward, after multiplication by the field factor. -/
example : (32 * 11 * 9 * 25 : ℕ) / 7 = 11314 := by norm_num

/-- The proposed scalar threshold is genuinely below the certified high-rate endpoint. -/
example : (540 : ℝ) < (23 / 4) ^ 2 * Real.exp (23 / 8) :=
  SharperBand.band_endpoint_constant_gt

/-- An over-budget threshold is empty, although an unguarded truncated binomial is one. -/
example (i : Fin 3) :
    (Finset.univ.filter fun u : OrdinarySimplex 3 2 ↦ 3 ≤ u.1 i).card = 0 := by
  rw [card_simplex_coordinate_tail]
  norm_num [simplexTailCount]

example : (2 - 3 + 3 : ℕ).choose 3 = 1 := by norm_num

/-- Two distinct coordinate shifts have exactly the combined residual budget. -/
example :
    (Finset.univ.filter fun u : OrdinarySimplex 2 3 ↦ 1 ≤ u.1 0 ∧ 1 ≤ u.1 1).card = 3 := by
  rw [card_simplex_coordinate_joint_tail 0 1 (by decide)]
  norm_num [simplexTailCount]

example : simplexTailRatio 3 5 2 = (5 / 14 : ℝ) := by
  norm_num [simplexTailRatio, simplexTailCount, Nat.choose]

/-- A nonintegral lower bound is an inequality, not a claim that a fractional count is attained. -/
example : (15 / 4 : ℝ) ≤
    ((Finset.univ.filter fun u : OrdinarySimplex 2 3 ↦ 2 ≤ Finset.univ.sup u.1).card : ℝ) := by
  have h := simplex_max_tail_count_lower 2 3 2
  norm_num [simplexTailRatio, simplexTailCount, card_ordinarySimplex, Nat.choose] at h ⊢
  exact h

/-- The exponential lower bound includes the zero-dimensional, zero-budget case. -/
example : Real.exp 0 ≤ simplexTailRatio 0 0 0 := by
  simpa using exp_lower_le_simplexTailRatio (r := 0) (W := 0) (t := 0) (by omega)

open Lean Elab Command in
run_cmd do
  let declarations : Array Name := #[
    ``natCard_boundedSolution_le_div_of_separant_budget,
    ``seven_mul_natCard_boundedSolution_le_of_separant_budget,
    ``natCard_boundedSolution_le_div_seven_of_interpolation_degree,
    ``agreeingPolynomials_encard_le_div_seven_of_band_certificate,
    ``strong_band_pointwise_div_seven,
    ``strong_band_certificate_div_seven,
    ``strong_band_certificate_five,
    ``sum_partitionGaps,
    ``sum_weighted_partitionGaps,
    ``partitionGaps_with_permutation_injective,
    ``simplex_max_event_card_le_band_mul_factorial,
    ``asymmetricBand_card_lower_of_max_event_mass,
    ``SharperBand.finrank_asymmetricBandLocalConstraint_le_normalized_of_band_card_lower,
    ``SharperBand.band_prescribed_endpoint_gt,
    ``SharperBand.band_prescribed_gap_multiplicity,
    ``ordinarySimplexLowerBoundsEquiv,
    ``card_simplex_lower_bounds,
    ``card_simplex_coordinate_tail,
    ``card_simplex_coordinate_joint_tail,
    ``simplexTailRatio_eq_prod,
    ``simplexTailRatio_add_le_mul,
    ``sum_simplexThresholdStatistic,
    ``sum_sq_simplexThresholdStatistic_le,
    ``simplex_max_tail_count_lower,
    ``simplex_max_tail_count_upper,
    ``simplex_max_band_count_lower,
    ``asymmetricBand_card_lower_of_tail_ratios,
    ``asymmetricBand_card_lower_of_tail_margins,
    ``SharperBand.finrank_asymmetricBandLocalConstraint_le_normalized_of_tail_margins,
    ``exp_lower_le_simplexTailRatio,
    ``simplexTailRatio_le_exp_upper]
  let accepted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    let axioms ← collectAxioms decl
    let unexpected := axioms.filter fun axiomName ↦ !accepted.contains axiomName
    unless unexpected.isEmpty do
      throwError "Unexpected axioms for {decl}: {unexpected}"
    logInfo m!"PASS {decl}: {axioms}"
