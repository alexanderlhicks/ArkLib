/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexCoordinateTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential bounds for exact finite simplex tails

The product formula gives a lower bound with the full finite quadratic error and an upper
bound retaining the denominator `W+r`. Both can be used without evaluating enormous binomial
coefficients. These inequalities still concern the discrete simplex, not a limiting law.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- Every factor in the feasible tail product is at least its first factor. -/
theorem pow_one_sub_le_simplexTailRatio {r W t : ℕ} (ht : t ≤ W) :
    (1 - (t : ℝ) / ((W : ℝ) + 1)) ^ r ≤ simplexTailRatio r W t := by
  rw [simplexTailRatio_eq_prod ht]
  have hz : 0 ≤ 1 - (t : ℝ) / ((W : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < (W : ℝ) + 1)]
    exact (Nat.cast_le.mpr ht).trans (le_add_of_nonneg_right zero_le_one)
  calc
    _ = ∏ _i ∈ Finset.range r, (1 - (t : ℝ) / ((W : ℝ) + 1)) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ ↦ hz)
      intro i _
      apply sub_le_sub_left
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg t)
        (by positivity : (0 : ℝ) < (W : ℝ) + 1) (by norm_num)

/-- A logarithmic lower bound retaining the full quadratic error near zero. -/
theorem neg_div_one_sub_le_log_one_sub {z : ℝ} (hz : z < 1) :
    -z / (1 - z) ≤ Real.log (1 - z) := by
  have hp : 0 < 1 - z := sub_pos.mpr hz
  have h := Real.one_sub_inv_le_log_of_pos hp
  have heq : 1 - (1 - z)⁻¹ = -z / (1 - z) := by
    field_simp
    ring
  rwa [heq] at h

/-- The lower exponential estimate for a feasible threshold.
Its exponent equals `-r*z-r*z²/(1-z)`, retaining the finite correction. -/
theorem exp_lower_le_simplexTailRatio {r W t : ℕ} (ht : t ≤ W) :
    let z := (t : ℝ) / ((W : ℝ) + 1)
    Real.exp (-(r : ℝ) * z / (1 - z)) ≤ simplexTailRatio r W t := by
  let z := (t : ℝ) / ((W : ℝ) + 1)
  have hz : z < 1 := by
    apply (div_lt_one (by positivity : (0 : ℝ) < (W : ℝ) + 1)).mpr
    have ht' : (t : ℝ) ≤ W := by exact_mod_cast ht
    linarith
  have hbase : Real.exp (-z / (1 - z)) ≤ 1 - z :=
    (Real.exp_le_exp.mpr (neg_div_one_sub_le_log_one_sub hz)).trans_eq
      (Real.exp_log (sub_pos.mpr hz))
  change Real.exp (-(r : ℝ) * z / (1 - z)) ≤ _
  calc
    _ = Real.exp (-z / (1 - z)) ^ r := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (1 - z) ^ r := pow_le_pow_left₀ (Real.exp_nonneg _) hbase r
    _ ≤ _ := pow_one_sub_le_simplexTailRatio ht

/-- The upper exponential estimate includes thresholds beyond the budget.
Positive dimension makes the denominator `W+r` explicitly positive. -/
theorem simplexTailRatio_le_exp_upper (r W t : ℕ) (hr : 0 < r) :
    simplexTailRatio r W t ≤ Real.exp (-(r : ℝ) * t / ((W : ℝ) + r)) := by
  by_cases ht : t ≤ W
  · rw [simplexTailRatio_eq_prod ht]
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    calc
      _ ≤ ∏ _i ∈ Finset.range r, Real.exp (-(t : ℝ) / ((W : ℝ) + r)) := by
        apply Finset.prod_le_prod
        · intro i _
          rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < (W : ℝ) + i + 1)]
          have ht' : (t : ℝ) ≤ W := by exact_mod_cast ht
          have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
          linarith
        · intro i hi
          have hi' : (i : ℝ) + 1 ≤ r := by exact_mod_cast Finset.mem_range.mp hi
          have hfrac : (t : ℝ) / ((W : ℝ) + r) ≤ (t : ℝ) / ((W : ℝ) + i + 1) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg t) (by positivity) (by linarith)
          have hbase := Real.add_one_le_exp (-(t : ℝ) / ((W : ℝ) + i + 1))
          have hexp := Real.exp_le_exp.mpr (neg_le_neg hfrac)
          simp only [neg_div] at hbase ⊢
          linarith
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
        congr 1
        ring
  · rw [simplexTailRatio_eq_zero_of_lt (Nat.lt_of_not_ge ht)]
    exact (Real.exp_pos _).le

end

end ReedSolomon.HiddenDerivative
