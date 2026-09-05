/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexCoordinateTail
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexPartitionCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite maximum-coordinate tails and band mass

The indicator sum for threshold exceedances has mean `μ = r * p(t)` and second moment at
most `μ + μ²`. Cauchy--Schwarz therefore gives maximum-tail mass at least `μ/(1+μ)`.
An upper union bound at `Cmax+1` yields band mass at least `μ/(1+μ)-ν`, which transports
through the proved partition-counting bridge. No coordinate independence is assumed.

The uniform numerical estimates at the prescribed all-rate parameters remain separate:
the final theorem exposes `11 ≤ μ` and `ν ≤ 13/50` as its only tail-mass premises.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- The real-valued indicator sum counting coordinates at least the threshold. -/
def simplexThresholdStatistic {r W : ℕ} (t : ℕ) (u : OrdinarySimplex r W) : ℝ :=
  ∑ i, if t ≤ u.1 i then 1 else 0

/-- Every threshold statistic is nonnegative. -/
theorem simplexThresholdStatistic_nonneg {r W t : ℕ} (u : OrdinarySimplex r W) :
    0 ≤ simplexThresholdStatistic t u := by
  unfold simplexThresholdStatistic
  exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

private theorem tail_count_eq_card_mul_ratio (r W t : ℕ) :
    (simplexTailCount r W t : ℝ) =
      Fintype.card (OrdinarySimplex r W) * simplexTailRatio r W t := by
  rw [card_ordinarySimplex, simplexTailRatio]
  have hden := (simplex_tail_denominator_pos r W).ne'
  field_simp

private theorem sum_threshold_indicator {r W t : ℕ} (i : Fin r) :
    (∑ u : OrdinarySimplex r W, if t ≤ u.1 i then (1 : ℝ) else 0) =
      Fintype.card (OrdinarySimplex r W) * simplexTailRatio r W t := by
  rw [← tail_count_eq_card_mul_ratio, ← card_simplex_coordinate_tail i]
  simp [Finset.sum_boole]

/-- The exact unnormalized first moment of the threshold statistic. -/
theorem sum_simplexThresholdStatistic (r W t : ℕ) :
    (∑ u : OrdinarySimplex r W, simplexThresholdStatistic t u) =
      Fintype.card (OrdinarySimplex r W) * ((r : ℝ) * simplexTailRatio r W t) := by
  unfold simplexThresholdStatistic
  rw [Finset.sum_comm]
  simp only [sum_threshold_indicator, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Negative correlation bounds the second moment, without an independence hypothesis. -/
theorem sum_sq_simplexThresholdStatistic_le (r W t : ℕ) :
    (∑ u : OrdinarySimplex r W, simplexThresholdStatistic t u ^ 2) ≤
      Fintype.card (OrdinarySimplex r W) *
        ((r : ℝ) * simplexTailRatio r W t + ((r : ℝ) * simplexTailRatio r W t) ^ 2) := by
  let C : ℝ := Fintype.card (OrdinarySimplex r W)
  let p := simplexTailRatio r W t
  let I := fun (i : Fin r) (u : OrdinarySimplex r W) ↦ if t ≤ u.1 i then (1 : ℝ) else 0
  have hp : 0 ≤ p := simplexTailRatio_nonneg r W t
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hpair : ∀ i j : Fin r, (∑ u, I i u * I j u) ≤
      C * ((if i = j then p else 0) + p ^ 2) := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hsq : ∀ u, I i u * I i u = I i u := by
        intro u
        simp only [I]
        split_ifs <;> norm_num
      simp only [hsq, if_true]
      have hm := sum_threshold_indicator (W := W) (t := t) i
      change (∑ u, I i u) = C * p at hm
      rw [hm]
      nlinarith only [mul_nonneg hC (sq_nonneg p)]
    · have hind : ∀ u, I i u * I j u =
          if t ≤ u.1 i ∧ t ≤ u.1 j then (1 : ℝ) else 0 := by
        intro u
        simp only [I]
        split_ifs <;> simp_all
      have hjoint : (∑ u, I i u * I j u) =
          C * simplexTailRatio r W (t + t) := by
        simp only [hind]
        rw [← tail_count_eq_card_mul_ratio, ← card_simplex_coordinate_joint_tail i j hij]
        simp [Finset.sum_boole]
      rw [hjoint, if_neg hij]
      have h := mul_le_mul_of_nonneg_left (simplexTailRatio_add_le_mul r W t t) hC
      simpa only [zero_add, pow_two] using h
  calc
    _ = ∑ i : Fin r, ∑ j : Fin r, ∑ u, I i u * I j u := by
      simp only [simplexThresholdStatistic, pow_two, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin r, ∑ j : Fin r, C * ((if i = j then p else 0) + p ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpair i j
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [C, p]
      ring

private theorem threshold_statistic_eq_zero_of_max_lt {r W t : ℕ}
    (u : OrdinarySimplex r W) (h : Finset.univ.sup u.1 < t) :
    simplexThresholdStatistic t u = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (Nat.not_le.mpr ((Finset.le_sup (Finset.mem_univ i)).trans_lt h))

/-- The second-moment maximum-tail bound. It includes zero mean and empty coordinate sets. -/
theorem simplex_max_tail_count_lower (r W t : ℕ) :
    let μ := (r : ℝ) * simplexTailRatio r W t
    Fintype.card (OrdinarySimplex r W) * (μ / (1 + μ)) ≤
      ((Finset.univ.filter fun u : OrdinarySimplex r W ↦ t ≤ Finset.univ.sup u.1).card : ℝ) := by
  let C : ℝ := Fintype.card (OrdinarySimplex r W)
  let μ := (r : ℝ) * simplexTailRatio r W t
  let Z := fun u : OrdinarySimplex r W ↦ simplexThresholdStatistic t u
  let event := Finset.univ.filter fun u : OrdinarySimplex r W ↦ t ≤ Finset.univ.sup u.1
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast card_ordinarySimplex_pos r W
  have hμ : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg r) (simplexTailRatio_nonneg r W t)
  have hmean : ∑ u, Z u = C * μ := sum_simplexThresholdStatistic r W t
  have hsecond : (∑ u, Z u ^ 2) ≤ C * (μ + μ ^ 2) :=
    sum_sq_simplexThresholdStatistic_le r W t
  have hsum : (∑ u ∈ event, Z u) = ∑ u, Z u := by
    apply Finset.sum_subset (Finset.subset_univ event)
    intro u _ hu
    have hu' : Finset.univ.sup u.1 < t := by
      simpa only [event, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hu
    exact threshold_statistic_eq_zero_of_max_lt u hu'
  have hsq : (∑ u ∈ event, Z u ^ 2) ≤ ∑ u, Z u ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ event)
      (fun _ _ _ ↦ sq_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq event (fun _ ↦ (1 : ℝ)) Z
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, hmean] at hCS
  have hbound : (C * μ) ^ 2 ≤ (event.card : ℝ) * (C * (μ + μ ^ 2)) :=
    hCS.trans (mul_le_mul_of_nonneg_left (hsq.trans hsecond) (Nat.cast_nonneg _))
  change C * (μ / (1 + μ)) ≤ (event.card : ℝ)
  by_cases hz : μ = 0
  · simp [hz]
  · have hμpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 1 + μ)).mpr
    apply (mul_le_mul_iff_left₀ (mul_pos hC hμpos)).mp
    nlinarith only [hbound]

/-- The finite union bound for a positive maximum threshold.
Positivity is necessary in dimension zero, whose empty maximum is zero. -/
theorem simplex_max_tail_count_upper (r W t : ℕ) (ht : 0 < t) :
    ((Finset.univ.filter fun u : OrdinarySimplex r W ↦ t ≤ Finset.univ.sup u.1).card : ℝ) ≤
      Fintype.card (OrdinarySimplex r W) * ((r : ℝ) * simplexTailRatio r W t) := by
  let event := Finset.univ.filter fun u : OrdinarySimplex r W ↦ t ≤ Finset.univ.sup u.1
  calc
    _ = ∑ _u ∈ event, (1 : ℝ) := by simp [event]
    _ ≤ ∑ u ∈ event, simplexThresholdStatistic t u := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨i, _, hi⟩ := (Finset.le_sup_iff ht).mp (Finset.mem_filter.mp hu).2
      calc
        (1 : ℝ) = (if t ≤ u.1 i then 1 else 0) := (if_pos hi).symm
        _ ≤ simplexThresholdStatistic t u := by
          apply Finset.single_le_sum (f := fun j ↦ if t ≤ u.1 j then (1 : ℝ) else 0)
            (fun j _ ↦ by split_ifs <;> norm_num) (Finset.mem_univ i)
    _ ≤ ∑ u, simplexThresholdStatistic t u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ event)
        (fun u _ _ ↦ simplexThresholdStatistic_nonneg u)
    _ = _ := sum_simplexThresholdStatistic r W t

/-- Lower second-moment mass minus the upper union-bound loss gives a maximum band. -/
theorem simplex_max_band_count_lower (r W Cmin Cmax : ℕ) :
    let μ := (r : ℝ) * simplexTailRatio r W Cmin
    let ν := (r : ℝ) * simplexTailRatio r W (Cmax + 1)
    Fintype.card (OrdinarySimplex r W) * (μ / (1 + μ) - ν) ≤
      ((Finset.univ.filter fun u : OrdinarySimplex r W ↦
        Cmin ≤ Finset.univ.sup u.1 ∧ Finset.univ.sup u.1 ≤ Cmax).card : ℝ) := by
  classical
  let lower := Finset.univ.filter fun u : OrdinarySimplex r W ↦ Cmin ≤ Finset.univ.sup u.1
  let upper := Finset.univ.filter fun u : OrdinarySimplex r W ↦ Cmax + 1 ≤ Finset.univ.sup u.1
  let band := Finset.univ.filter fun u : OrdinarySimplex r W ↦
    Cmin ≤ Finset.univ.sup u.1 ∧ Finset.univ.sup u.1 ≤ Cmax
  have hcover : lower ⊆ band ∪ upper := by
    intro u hu
    have hl := (Finset.mem_filter.mp hu).2
    by_cases hi : Finset.univ.sup u.1 ≤ Cmax
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hl, hi⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ u, by omega⟩))
  have hc : lower.card ≤ band.card + upper.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hc' : (lower.card : ℝ) ≤ band.card + upper.card := by exact_mod_cast hc
  have hl := simplex_max_tail_count_lower r W Cmin
  have hu := simplex_max_tail_count_upper r W (Cmax + 1) (Nat.succ_pos Cmax)
  change _ ≤ (lower.card : ℝ) at hl
  change (upper.card : ℝ) ≤ _ at hu
  change _ ≤ (band.card : ℝ)
  nlinarith only [hc', hl, hu]

/-- The finite maximum-tail inequality feeds the existing normalized partition-count bridge. -/
theorem asymmetricBand_card_lower_of_tail_ratios {d W Cmin Cmax : ℕ}
    (mass : ℝ) (hmass : 0 ≤ mass)
    (hbound : mass ≤
      ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin /
        (1 + ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin) -
      ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W (Cmax + 1)) :
    mass * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      (asymmetricBandTuples d W Cmin Cmax).card := by
  apply asymmetricBand_card_lower_of_max_event_mass mass hmass
  have h := mul_le_mul_of_nonneg_left hbound
    (Nat.cast_nonneg (Fintype.card (OrdinarySimplex (d - 1) W)) : (0 : ℝ) ≤ _)
  calc
    _ = (Fintype.card (OrdinarySimplex (d - 1) W) : ℝ) * mass := mul_comm _ _
    _ ≤ _ := h
    _ ≤ _ := simplex_max_band_count_lower _ _ _ _

/-- The proposed rational margins suffice for `13/20` band mass, with all finite counting proved.
Only the numerical tail estimates at the chosen parameters remain to be supplied. -/
theorem asymmetricBand_card_lower_of_tail_margins {d W Cmin Cmax : ℕ}
    (hlower : (11 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin)
    (hupper : ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W (Cmax + 1) ≤ 13 / 50) :
    (13 / 20 : ℝ) * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      (asymmetricBandTuples d W Cmin Cmax).card := by
  apply asymmetricBand_card_lower_of_tail_ratios (13 / 20) (by norm_num)
  have hden : (0 : ℝ) <
      1 + ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin := by linarith
  have hfrac : (11 / 12 : ℝ) ≤
      ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin /
        (1 + ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  linarith

end

end ReedSolomon.HiddenDerivative
