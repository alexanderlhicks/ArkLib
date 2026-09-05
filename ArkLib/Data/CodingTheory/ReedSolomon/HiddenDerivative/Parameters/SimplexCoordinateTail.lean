/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexMoments
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact coordinate tails of an ordinary simplex

Subtracting prescribed coordinate lower bounds gives a smaller ordinary simplex. If their
sum exceeds the budget, the event is empty: truncated subtraction must not be used alone.
The resulting tail ratio has a finite product formula and is negatively correlated under
two coordinate shifts. These are exact discrete identities, not volume approximations.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- Subtracting feasible coordinate lower bounds preserves precisely the residual budget. -/
def ordinarySimplexLowerBoundsEquiv {r W : ℕ} (a : Fin r → ℕ) (ha : ∑ i, a i ≤ W) :
    {u : OrdinarySimplex r W // ∀ i, a i ≤ u.1 i} ≃
      OrdinarySimplex r (W - ∑ i, a i) where
  toFun u := ⟨fun i ↦ u.1.1 i - a i, by
    have hsum : (∑ i, (u.1.1 i - a i)) + ∑ i, a i = ∑ i, u.1.1 i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ Nat.sub_add_cancel (u.2 i))
    have := u.1.2
    change (∑ i, (u.1.1 i - a i)) ≤ W - ∑ i, a i
    omega⟩
  invFun v := ⟨⟨fun i ↦ v.1 i + a i, by
    rw [Finset.sum_add_distrib]
    have := v.2
    omega⟩, fun i ↦ Nat.le_add_left _ _⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Nat.sub_add_cancel (u.2 i)
  right_inv v := by
    apply Subtype.ext
    funext i
    exact Nat.add_sub_cancel _ _

/-- Exact cardinality for simultaneous coordinate lower bounds, including infeasible shifts. -/
theorem card_simplex_lower_bounds {r W : ℕ} (a : Fin r → ℕ) :
    (Finset.univ.filter fun u : OrdinarySimplex r W ↦ ∀ i, a i ≤ u.1 i).card =
      if (∑ i, a i) ≤ W then (W - (∑ i, a i) + r).choose r else 0 := by
  classical
  by_cases ha : (∑ i, a i) ≤ W
  · rw [if_pos ha, ← Fintype.card_subtype]
    exact (Fintype.card_congr (ordinarySimplexLowerBoundsEquiv a ha)).trans
      (card_ordinarySimplex _ _)
  · rw [if_neg ha]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact ha ((Finset.sum_le_sum fun i _ ↦ (Finset.mem_filter.mp hu).2 i).trans u.2)

/-- The exact residual-simplex count. The feasibility guard is essential. -/
def simplexTailCount (r W t : ℕ) : ℕ :=
  if t ≤ W then (W - t + r).choose r else 0

/-- The uniform coordinate-tail ratio in positive dimension; its denominator is always positive.
In dimension zero this is only an algebraic extension of the formula, not a coordinate event. -/
def simplexTailRatio (r W t : ℕ) : ℝ :=
  simplexTailCount r W t / (W + r).choose r

/-- Counting one coordinate tail by shifting just that coordinate. -/
theorem card_simplex_coordinate_tail {r W t : ℕ} (i : Fin r) :
    (Finset.univ.filter fun u : OrdinarySimplex r W ↦ t ≤ u.1 i).card =
      simplexTailCount r W t := by
  classical
  have h := card_simplex_lower_bounds (W := W) (Pi.single i t)
  have hpred : ∀ u : OrdinarySimplex r W,
      (∀ j, (Pi.single i t : Fin r → ℕ) j ≤ u.1 j) ↔ t ≤ u.1 i := by
    intro u
    constructor
    · intro hu
      simpa using hu i
    · intro hu j
      by_cases hji : j = i
      · subst j
        simpa using hu
      · simp [hji]
  simp only [hpred] at h
  simpa [Pi.single_apply, simplexTailCount] using h

/-- Distinct-coordinate joint tails shift the total budget by the sum of the thresholds. -/
theorem card_simplex_coordinate_joint_tail {r W s t : ℕ} (i j : Fin r) (hij : i ≠ j) :
    (Finset.univ.filter fun u : OrdinarySimplex r W ↦ s ≤ u.1 i ∧ t ≤ u.1 j).card =
      simplexTailCount r W (s + t) := by
  classical
  have h := card_simplex_lower_bounds (W := W)
    (fun k ↦ (Pi.single i s : Fin r → ℕ) k + (Pi.single j t : Fin r → ℕ) k)
  have hpred : ∀ u : OrdinarySimplex r W,
      (∀ k, (Pi.single i s : Fin r → ℕ) k + (Pi.single j t : Fin r → ℕ) k ≤ u.1 k) ↔
        s ≤ u.1 i ∧ t ≤ u.1 j := by
    intro u
    constructor
    · intro hu
      exact ⟨by simpa [Pi.single_apply, hij, hij.symm] using hu i,
        by simpa [Pi.single_apply, hij, hij.symm] using hu j⟩
    · intro hu k
      by_cases hki : k = i
      · subst k
        simpa [Pi.single_apply, hij, hij.symm] using hu.1
      · by_cases hkj : k = j
        · subst k
          simpa [Pi.single_apply, hij, hij.symm] using hu.2
        · simp [hki, hkj]
  simp only [hpred] at h
  simpa [Finset.sum_add_distrib, Pi.single_apply, simplexTailCount] using h

/-- The normalizing simplex cardinality is nonzero even in dimension or budget zero. -/
theorem simplex_tail_denominator_pos (r W : ℕ) : (0 : ℝ) < (W + r).choose r := by
  exact_mod_cast Nat.choose_pos (Nat.le_add_left _ _)

/-- Tail ratios are nonnegative, including infeasible thresholds. -/
theorem simplexTailRatio_nonneg (r W t : ℕ) : 0 ≤ simplexTailRatio r W t := by
  unfold simplexTailRatio
  positivity

/-- An infeasible coordinate threshold has probability zero. -/
theorem simplexTailRatio_eq_zero_of_lt {r W t : ℕ} (h : W < t) :
    simplexTailRatio r W t = 0 := by
  simp [simplexTailRatio, simplexTailCount, Nat.not_le.mpr h]

private theorem factorial_mul_choose_eq_prod (r W : ℕ) :
    (r.factorial : ℝ) * (W + r).choose r =
      ∏ i ∈ Finset.range r, ((W : ℝ) + i + 1) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose W r
  rw [Nat.ascFactorial_eq_prod_range] at h
  exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm)

/-- The exact tail ratio is a finite product when the threshold fits the budget. -/
theorem simplexTailRatio_eq_prod {r W t : ℕ} (ht : t ≤ W) :
    simplexTailRatio r W t =
      ∏ i ∈ Finset.range r, (1 - (t : ℝ) / ((W : ℝ) + i + 1)) := by
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hnum := factorial_mul_choose_eq_prod r (W - t)
  have hden := factorial_mul_choose_eq_prod r W
  simp only [Nat.cast_sub ht] at hnum
  unfold simplexTailRatio simplexTailCount
  rw [if_pos ht]
  calc
    _ = ((r.factorial : ℝ) * (W - t + r).choose r) /
        ((r.factorial : ℝ) * (W + r).choose r) := by rw [mul_div_mul_left _ _ hf]
    _ = (∏ i ∈ Finset.range r, ((W : ℝ) - t + i + 1)) /
        (∏ i ∈ Finset.range r, ((W : ℝ) + i + 1)) := by rw [hnum, hden]
    _ = _ := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro i _
      have hi : (0 : ℝ) < (W : ℝ) + i + 1 := by positivity
      field_simp
      ring

/-- Two nonnegative coordinate shifts are negatively correlated in the finite simplex.
The statement includes over-budget thresholds and dimension zero. -/
theorem simplexTailRatio_add_le_mul (r W s t : ℕ) :
    simplexTailRatio r W (s + t) ≤ simplexTailRatio r W s * simplexTailRatio r W t := by
  by_cases hst : s + t ≤ W
  · have hs : s ≤ W := by omega
    have ht : t ≤ W := by omega
    rw [simplexTailRatio_eq_prod hst, simplexTailRatio_eq_prod hs,
      simplexTailRatio_eq_prod ht, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro i _
      have hden : (0 : ℝ) < (W : ℝ) + i + 1 := by positivity
      have hst' : (s : ℝ) + t ≤ W := by exact_mod_cast hst
      rw [sub_nonneg, div_le_one hden]
      simp only [Nat.cast_add]
      linarith
    · intro i _
      have hden : (0 : ℝ) < (W : ℝ) + i + 1 := by positivity
      have hprod : 0 ≤ ((s : ℝ) / ((W : ℝ) + i + 1)) *
          ((t : ℝ) / ((W : ℝ) + i + 1)) := by positivity
      simp only [Nat.cast_add]
      rw [add_div]
      nlinarith only [hprod]
  · rw [simplexTailRatio_eq_zero_of_lt (Nat.lt_of_not_ge hst)]
    exact mul_nonneg (simplexTailRatio_nonneg r W s) (simplexTailRatio_nonneg r W t)

end

end ReedSolomon.HiddenDerivative
