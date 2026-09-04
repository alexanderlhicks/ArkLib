/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBand

/-!
# Asymmetric-band boundary checks

These checks distinguish the lower support edge from a one-sided cutoff and the strict real
threshold from its floor. The dimension theorem is also instantiated at `d = D = 1`: this is
valid for the coarse band support, although the landed exact space needs `d < D`.
-/

namespace ReedSolomon.HiddenDerivative

/-- The band keeps the lower edge itself. -/
example : (fun _ : Fin (2 - 1) ↦ 1) ∈ asymmetricBandTuples 2 3 1 2 := by
  rw [mem_asymmetricBandTuples]
  decide

/-- The lower edge rejects the zero higher-jet tuple. -/
example : (fun _ : Fin (2 - 1) ↦ 0) ∉ asymmetricBandTuples 2 3 1 2 := by
  rw [mem_asymmetricBandTuples]
  decide

/-- The upper edge rejects degree three even when the weight budget permits it. -/
example : (fun _ : Fin (2 - 1) ↦ 3) ∉ asymmetricBandTuples 2 3 1 2 := by
  rw [mem_asymmetricBandTuples]
  decide

/-- A nonintegral cutoff admits the integer immediately below its ceiling. -/
example (u : JetVariable 1 →₀ ℕ) (hu : u none + 2 * totalJetDegree u = 3) :
    (u none + 2 * totalJetDegree u : ℕ) < (7 / 2 : ℝ) := by
  rw [hu]
  norm_num

/-- At an integral cutoff, equality is excluded. -/
example (u : JetVariable 1 →₀ ℕ) (hu : u none + 2 * totalJetDegree u = 3) :
    ¬((u none + 2 * totalJetDegree u : ℕ) < (3 : ℝ)) := by
  rw [hu]
  norm_num

/-- Coarse band finiteness and dimension do not require `d < D`. -/
example : Module.finrank ℚ (asymmetricBandSpace ℚ 1 1 2 0 0 0 5 (by decide)) =
    asymmetricBandDimensionCount 1 1 2 0 0 0 5 :=
  finrank_asymmetricBandSpace_eq_dimensionCount (by decide) (by decide)

/-- The local-coordinate count uses `d+1` and ceiling division. -/
example : asymmetricBandLocalBudget 2 4 0 1 = 11 := by
  decide

end ReedSolomon.HiddenDerivative
