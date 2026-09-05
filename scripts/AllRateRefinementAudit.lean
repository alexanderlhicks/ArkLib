/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.StrongBand
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandNormalizedRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SharperBandEndpoint
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexPartitionCounting
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
    ``SharperBand.band_prescribed_gap_multiplicity]
  let accepted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    let axioms ← collectAxioms decl
    let unexpected := axioms.filter fun axiomName ↦ !accepted.contains axiomName
    unless unexpected.isEmpty do
      throwError "Unexpected axioms for {decl}: {unexpected}"
    logInfo m!"PASS {decl}: {axioms}"
