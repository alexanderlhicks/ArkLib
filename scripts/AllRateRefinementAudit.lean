/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.StrongBand
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.RefinedBand
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandNormalizedRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandComparison
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SharperBandEndpoint
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.TunableBandEndpoint
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexPartitionCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexMaximumTail
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexTailBounds
import Lean.Util.CollectAxioms

/-!
# Focused all-rate refinement audit

Run with `lake env lean --trust=0 scripts/AllRateRefinementAudit.lean` after building its imports.
Missing declarations and any axiom beyond the accepted logical baseline fail this command.
The repository-wide axiom sweep remains a separate integration gate.

This audits the full `5.5` construction and quantitative all-rate theorem, together with the
finite counting and analytic lemmas on which they depend. No runtime theorem is asserted.
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

/-- The new coefficient fits below the certified simplex fraction, without floating point. -/
example : (1 / 140 : ℝ) ≤ (17499 / 50000) ^ 3 / 6 := by norm_num

/-- Both ceiling errors fit at the exact multiplicity threshold. -/
example : ⌈(17499 / 50000 : ℝ) * 1 * 100000⌉₊ ≤ 100000 + 1 ∧
    7 * (165000 + ⌈(17499 / 50000 : ℝ) * 1 * 100000⌉₊) ≤ ⌈(1400000 : ℝ)⌉₊ := by
  exact asymmetricBand_simplex_scalar_conditions_of_slack
    (m := 100000) (D := 7) (Cmax := 165000) (L := 1400000)
    (g := 1) (β := 13 / 20) (θ := 17499 / 50000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Taking all the limiting `7/20` fraction without a rounding reserve is unsafe. -/
example : ⌈(1 + 13 / 20 : ℝ)⌉₊ + ⌈(7 / 20 : ℝ)⌉₊ > ⌈(2 : ℝ)⌉₊ := by
  have hupper : ⌈(1 + 13 / 20 : ℝ)⌉₊ = 2 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  have hside : ⌈(7 / 20 : ℝ)⌉₊ = 1 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  rw [hupper, hside]
  norm_num

/-- The improved scalar certificate includes an actual finite gap and a high rate. -/
example :
    let d := Nat.ceil (Real.exp ((11 / 2 : ℝ) / (1 / 10)))
    (1400 / 3 : ℝ) < (d : ℝ) ^ ((1 / 9 : ℝ) / (2 + 1 / 9)) *
      (harmonic (d - 1) : ℝ) ^ 2 * (9 / 10) * (1 / 9) ^ 2 / (1 + (1 / 9) / 2) ^ 2 := by
  have h := band_prescribed_endpoint_div_140_gt (1 / 10) (9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show min (1 : ℝ) ((1 / 10) / (9 / 10)) = 1 / 9 by norm_num] at h
  exact h

/-- The small-gap order really uses `5.5`, not the old order hidden behind a numerical bound. -/
example : refinedDerivativeOrder (1 / 10) = Nat.ceil (Real.exp 55) := by
  rw [refinedDerivativeOrder_eq_ceil (by norm_num : (1 / 10 : ℝ) < 1 / 4)]
  norm_num

/-- The exact quarter boundary retains the separately proved order-zero regime. -/
example : refinedDerivativeOrder (1 / 4) = 0 := refinedDerivativeOrder_eq_zero le_rfl

/-- No padding room is hidden in the improved canonical theorem: specialize to `n=q`.
The domain is still an arbitrary injection and the original message dimension is retained. -/
example {δ : ℝ} {q k : ℕ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ q) (hk : 0 < k) (hkq : k ≤ q)
    (hq : q.Prime) (domain : Fin q ↪ ZMod q) :
    Code.Lambda (ReedSolomon.code domain k : Set (Fin q → ZMod q))
      (capacityRadius δ q k) ≤
        (((32 * (refinedDerivativeOrder δ + 1) * refinedBandMultiplicity δ ^ 2 *
          q ^ (2 * refinedDerivativeOrder δ)) / 7 : ℕ) : ℕ∞) := by
  obtain ⟨certificate⟩ := refined_band_certificate_div_seven
    hδ hδ' hblock hk hkq hq le_rfl domain
  exact certificate.lambda_le

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
    ``simplexTailRatio_le_exp_upper,
    ``asymmetricBand_simplex_scalar_conditions_of_slack,
    ``finrank_asymmetricBandSpace_ge_cubic_of_slack,
    ``finrank_asymmetricBandSpace_ge_cubic_div_140,
    ``finrank_asymmetricBandSpace_ge_prescribed_cubic_div_140,
    ``band_prescribed_endpoint_lower_of_constant,
    ``band_prescribed_endpoint_div_140_gt,
    ``band_gap_multiplicity_of_constant,
    ``band_lower_tail_exp_margin_div_140,
    ``band_upper_tail_exp_margin_div_140,
    ``SharperBand.band_scalar_comparison_div_140,
    ``SharperBand.band_budget_lt_dimensionCount_of_mass_and_endpoint,
    ``SharperBand.exists_nonzero_band_interpolant_of_mass_and_endpoint,
    ``asymmetricBand_card_lower_of_tail_bounds,
    ``asymmetricBand_card_lower_of_tighter_tail_margins,
    ``band_thousand_sq_add_one_le_exp,
    ``band_harmonic_simplex_errors,
    ``band_simplex_lower_exponent,
    ``band_simplex_upper_exponent,
    ``asymmetricBand_mass_of_simplex_parameters,
    ``band_block_size_bounds_of_constant,
    ``refinedDerivativeOrder_le_strong,
    ``refinedBandMultiplicity_le_strong,
    ``refined_band_rate_parameter_estimates,
    ``refined_band_budget_lt_dimensionCount,
    ``refined_hidden_derivative_construction,
    ``refined_band_pointwise_div_seven,
    ``refined_band_certificate_div_seven,
    ``refined_band_pointwise_of_large_field,
    ``refined_band_certificate_of_large_field,
    ``refined_asymmetric_band,
    ``refined_quantitative_all_rate]
  let accepted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    let axioms ← collectAxioms decl
    let unexpected := axioms.filter fun axiomName ↦ !accepted.contains axiomName
    unless unexpected.isEmpty do
      throwError "Unexpected axioms for {decl}: {unexpected}"
    logInfo m!"PASS {decl}: {axioms}"
