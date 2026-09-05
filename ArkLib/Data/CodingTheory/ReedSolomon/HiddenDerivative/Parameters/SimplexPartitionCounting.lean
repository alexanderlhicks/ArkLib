/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexBandCounting
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm

/-!
# Sorting simplexes into higher-jet bands

Sort a nonnegative tuple in descending order and take consecutive differences, with a final zero.
The weighted sum of these differences is the original sum; their ordinary sum is its maximum.
Recording the sorting permutation makes the map injective, so every fiber has at most `r!` points.

This gives an exact finite band-count bridge without coordinatewise rounding loss. It does not
yet prove the uniform maximum-coordinate tail estimates needed for the proposed `13/20` mass.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- A permutation arranging the coordinates in descending order. -/
def descendingPermutation {r : ℕ} (u : Fin r → ℕ) : Equiv.Perm (Fin r) :=
  Tuple.sort (α := OrderDual ℕ) u

/-- Descending coordinates, extended by zero beyond the tuple. -/
def sortedCoordinate {r : ℕ} (u : Fin r → ℕ) (i : ℕ) : ℕ :=
  if hi : i < r then u (descendingPermutation u ⟨i, hi⟩) else 0

/-- Consecutive differences of descending coordinates. -/
def partitionGaps {r : ℕ} (u : Fin r → ℕ) (i : Fin r) : ℕ :=
  sortedCoordinate u i.val - sortedCoordinate u (i.val + 1)

@[simp]
theorem sortedCoordinate_apply {r : ℕ} (u : Fin r → ℕ) (i : Fin r) :
    sortedCoordinate u i.val = u (descendingPermutation u i) := by
  simp [sortedCoordinate]

@[simp]
theorem sortedCoordinate_end {r : ℕ} (u : Fin r → ℕ) : sortedCoordinate u r = 0 := by
  simp [sortedCoordinate]

/-- Zero extension preserves the descending order because coordinates are nonnegative. -/
theorem sortedCoordinate_antitone {r : ℕ} (u : Fin r → ℕ) :
    Antitone (sortedCoordinate u) := by
  intro i j hij
  by_cases hj : j < r
  · have hi : i < r := lt_of_le_of_lt hij hj
    have h := Tuple.monotone_sort (α := OrderDual ℕ) u
      (show (⟨i, hi⟩ : Fin r) ≤ ⟨j, hj⟩ from hij)
    change u (descendingPermutation u ⟨j, hj⟩) ≤
      u (descendingPermutation u ⟨i, hi⟩) at h
    simpa only [sortedCoordinate, dif_pos hi, dif_pos hj] using h
  · simp [sortedCoordinate, hj]

/-- The first sorted coordinate is the finite supremum, including the empty tuple. -/
theorem sortedCoordinate_zero_eq_sup {r : ℕ} (u : Fin r → ℕ) :
    sortedCoordinate u 0 = Finset.univ.sup u := by
  apply le_antisymm
  · by_cases hr : 0 < r
    · simpa [sortedCoordinate, hr] using
        (Finset.le_sup (f := u) (Finset.mem_univ (descendingPermutation u ⟨0, hr⟩)))
    · simp [sortedCoordinate, hr]
  · apply Finset.sup_le
    intro i _
    have h := sortedCoordinate_antitone u
      (Nat.zero_le ((descendingPermutation u).symm i).val)
    simpa only [sortedCoordinate_apply, Equiv.apply_symm_apply] using h

private theorem sum_gaps_add_last (x : ℕ → ℕ) (hx : Antitone x) (r : ℕ) :
    (∑ i ∈ Finset.range r, (x i - x (i + 1))) + x r = x 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have h := Nat.sub_add_cancel (hx (Nat.le_succ r))
    simp only [Nat.succ_eq_add_one] at h ⊢
    omega

private theorem sum_weighted_gaps_add_last (x : ℕ → ℕ) (hx : Antitone x) (r : ℕ) :
    (∑ i ∈ Finset.range r, (i + 1) * (x i - x (i + 1))) + r * x r =
      ∑ i ∈ Finset.range r, x i := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Finset.sum_range_succ]
    have h := Nat.sub_add_cancel (hx (Nat.le_succ r))
    nlinarith only [ih, h]

/-- The gap tuple's ordinary degree is exactly the largest original coordinate. -/
theorem sum_partitionGaps {r : ℕ} (u : Fin r → ℕ) :
    ∑ i, partitionGaps u i = Finset.univ.sup u := by
  have h := sum_gaps_add_last (sortedCoordinate u) (sortedCoordinate_antitone u) r
  simp only [sortedCoordinate_end, add_zero, sortedCoordinate_zero_eq_sup] at h
  calc
    _ = ∑ i ∈ Finset.range r, (sortedCoordinate u i - sortedCoordinate u (i + 1)) :=
      Fin.sum_univ_eq_sum_range _ r
    _ = _ := h

/-- The gap tuple's weighted sum is exactly the original coordinate sum. -/
theorem sum_weighted_partitionGaps {r : ℕ} (u : Fin r → ℕ) :
    ∑ i, (i.val + 1) * partitionGaps u i = ∑ i, u i := by
  have h := sum_weighted_gaps_add_last (sortedCoordinate u) (sortedCoordinate_antitone u) r
  simp only [sortedCoordinate_end, mul_zero, add_zero] at h
  calc
    _ = ∑ i ∈ Finset.range r, (i + 1) *
        (sortedCoordinate u i - sortedCoordinate u (i + 1)) := Fin.sum_univ_eq_sum_range _ r
    _ = ∑ i ∈ Finset.range r, sortedCoordinate u i := h
    _ = ∑ i : Fin r, sortedCoordinate u i.val := (Fin.sum_univ_eq_sum_range _ r).symm
    _ = ∑ i, u (descendingPermutation u i) := by simp
    _ = ∑ i, u i := Equiv.sum_comp (descendingPermutation u) u

private theorem antitone_eq_of_gaps_eq {x y : ℕ → ℕ} {r : ℕ}
    (hx : Antitone x) (hy : Antitone y) (hlast : x r = y r)
    (hgaps : ∀ i < r, x i - x (i + 1) = y i - y (i + 1)) :
    ∀ i ≤ r, x i = y i := by
  have hback : ∀ j, j ≤ r → x (r - j) = y (r - j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hlast
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hg := hgaps (r - (j + 1)) (by omega)
      have hx' := hx (Nat.le_succ (r - (j + 1)))
      have hy' := hy (Nat.le_succ (r - (j + 1)))
      have heq : r - j = r - (j + 1) + 1 := by omega
      simp only [heq] at hi
      simp only [Nat.succ_eq_add_one] at hx' hy'
      omega
  intro i hi
  simpa only [Nat.sub_sub_self hi] using hback (r - i) (Nat.sub_le _ _)

/-- The gaps together with the sorting permutation recover the original tuple. -/
theorem partitionGaps_with_permutation_injective (r : ℕ) :
    Function.Injective (fun u : Fin r → ℕ ↦ (partitionGaps u, descendingPermutation u)) := by
  intro u v huv
  have hg : partitionGaps u = partitionGaps v := congrArg Prod.fst huv
  have hp : descendingPermutation u = descendingPermutation v := congrArg Prod.snd huv
  have hseq := antitone_eq_of_gaps_eq (sortedCoordinate_antitone u)
    (sortedCoordinate_antitone v)
    (show sortedCoordinate u r = sortedCoordinate v r by simp)
    (fun i hi ↦ congrFun hg ⟨i, hi⟩)
  funext i
  have h := hseq ((descendingPermutation u).symm i).val (Nat.le_of_lt (Fin.isLt _))
  simp only [sortedCoordinate_apply, ← hp, Equiv.apply_symm_apply] at h
  exact h

/-- Maximum-coordinate bounds place the gap tuple directly in the existing asymmetric band. -/
theorem partitionGaps_mem_band {d W Cmin Cmax : ℕ}
    (u : OrdinarySimplex (d - 1) W)
    (hlo : Cmin ≤ Finset.univ.sup u.1) (hhi : Finset.univ.sup u.1 ≤ Cmax) :
    partitionGaps u.1 ∈ asymmetricBandTuples d W Cmin Cmax := by
  rw [mem_asymmetricBandTuples]
  simpa only [higherJetTupleWeight, higherJetTupleDegree, sum_weighted_partitionGaps,
    sum_partitionGaps] using And.intro u.2 (And.intro hlo hhi)

/-- The permutation coordinate bounds every maximum-band event by band size times `r!`.
No uniformity of orbit sizes and no coordinate-floor correction is required. -/
theorem simplex_max_event_card_le_band_mul_factorial {d W Cmin Cmax : ℕ}
    (event : Finset (OrdinarySimplex (d - 1) W))
    (hlo : ∀ u ∈ event, Cmin ≤ Finset.univ.sup u.1)
    (hhi : ∀ u ∈ event, Finset.univ.sup u.1 ≤ Cmax) :
    event.card ≤ (asymmetricBandTuples d W Cmin Cmax).card * (d - 1).factorial := by
  let f : ↥event → ↥(asymmetricBandTuples d W Cmin Cmax) × Equiv.Perm (Fin (d - 1)) :=
    fun u ↦ (⟨partitionGaps u.1.1, partitionGaps_mem_band u.1 (hlo u.1 u.2) (hhi u.1 u.2)⟩,
      descendingPermutation u.1.1)
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply partitionGaps_with_permutation_injective (d - 1)
    exact Prod.ext (congrArg (fun p ↦ p.1.1) huv)
      (congrArg (fun p : ↥(asymmetricBandTuples d W Cmin Cmax) ×
        Equiv.Perm (Fin (d - 1)) ↦ p.2) huv)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using h

/-- Any certified maximum-band mass yields the normalized lattice lower bound.
The mass is a finite cardinality premise; no asymptotic volume distribution is assumed. -/
theorem asymmetricBand_card_lower_of_max_event_mass {d W Cmin Cmax : ℕ}
    (mass : ℝ) (hmass : 0 ≤ mass)
    (hevent : mass * Fintype.card (OrdinarySimplex (d - 1) W) ≤
      ((Finset.univ.filter fun u : OrdinarySimplex (d - 1) W ↦
        Cmin ≤ Finset.univ.sup u.1 ∧ Finset.univ.sup u.1 ≤ Cmax).card : ℝ)) :
    mass * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      (asymmetricBandTuples d W Cmin Cmax).card := by
  let event := Finset.univ.filter fun u : OrdinarySimplex (d - 1) W ↦
    Cmin ≤ Finset.univ.sup u.1 ∧ Finset.univ.sup u.1 ≤ Cmax
  have hcard := simplex_max_event_card_le_band_mul_factorial event
    (fun _ hu ↦ (Finset.mem_filter.mp hu).2.1)
    (fun _ hu ↦ (Finset.mem_filter.mp hu).2.2)
  have hcard' : (event.card : ℝ) ≤
      (asymmetricBandTuples d W Cmin Cmax).card * ((d - 1).factorial : ℝ) := by
    exact_mod_cast hcard
  have hvolume : (W : ℝ) ^ (d - 1) ≤
      ((d - 1).factorial : ℝ) * Fintype.card (OrdinarySimplex (d - 1) W) := by
    exact_mod_cast pow_le_factorial_mul_card_ordinarySimplex (d - 1) W
  have hf : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  have h₁ := mul_le_mul_of_nonneg_left hvolume hmass
  have h₂ := mul_le_mul_of_nonneg_left hevent hf.le
  have h₃ := mul_le_mul_of_nonneg_left hcard' hf.le
  apply (div_le_iff₀ (sq_pos_of_pos hf)).mpr
  change mass * Fintype.card (OrdinarySimplex (d - 1) W) ≤ (event.card : ℝ) at hevent
  change ((d - 1).factorial : ℝ) *
    (mass * Fintype.card (OrdinarySimplex (d - 1) W)) ≤ _ at h₂
  nlinarith only [h₁, h₂, h₃]

end

end ReedSolomon.HiddenDerivative
