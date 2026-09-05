/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao

Adapted from AsymmetricBandNormalizedRank.lean at 075c6557.
The stronger band-cardinality premise is not proved in this file.
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandNormalizedRank
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexMaximumTail

/-!
# Sharper normalized rank conditional on a stronger finite band count

The `13/20` cardinality lower bound is an explicit premise throughout, not a new axiom.
It gives the coefficient `10/3` in place of `15/2`. The generic estimates are reused from
`AsymmetricBandNormalizedRank`; this file does not assert the proposed all-rate improvement.
This module assembles finite geometric budget and rounding estimates from the parameters of
[DKTZ26], source revision `9e4d6488ead94be47cca69e5be915b5667143b66`.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z.,
  *Reed--Solomon List Decoding up to Capacity at Every Rate*][DKTZ26]
-/

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative.SharperBand

open ReedSolomon.HiddenDerivative

/-- The stronger mass premise improves the scalar rank coefficient. -/
theorem improved_rank_constant_lt :
    (9 / 8 : ℝ) * (20 / 13) * (101 / 100) * (19 / 10) < 10 / 3 := by norm_num

/-- Scalar assembly of the normalized estimate, with every external numerical premise exposed. -/
theorem asymmetricBandLocalBudget_le_normalized_of_scalar_bounds
    (g H B : ℝ) (d m W Be : ℕ) (hg : 0 ≤ g) (hH : 0 < H) (hB : 0 ≤ B)
    (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hBe : (Be : ℝ) ≤ 9 / 8 * g * m)
    (hvolume : (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤ 20 / 13 * B)
    (hexp : Real.exp ((((d - 1 : ℕ) : ℝ) * m / W) *
      (1 + (d.choose 2 : ℝ) / m)) ≤ 19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2)))
    (hrec : 1 / (((d - 1 : ℕ) : ℝ) * m / W) ^ 2 +
      (d : ℝ) / (m * (((d - 1 : ℕ) : ℝ) * m / W)) ≤
        101 / 100 * (1 / (H / (1 + g / 2)) ^ 2)) :
    (asymmetricBandLocalBudget d m W Be : ℝ) ≤
      10 / 3 * g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
  have hk : 0 < κ := by
    have : 0 < d - 1 := by omega
    dsimp [κ]
    positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have ha : 1 + g / 2 ≠ 0 := by linarith
  have hbase := asymmetricBandLocalBudget_le_kappa d m W Be hd hm hW
  change (asymmetricBandLocalBudget d m W Be : ℝ) ≤ _ at hbase
  have hid : (m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ =
      (m : ℝ) ^ 2 / d * (1 / κ ^ 2 + (d : ℝ) / (m * κ)) := by
    field_simp
  change _ ≤ Be * _ * Real.exp (κ * _) *
    ((m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ) at hbase
  rw [hid] at hbase
  have hupper : (Be : ℝ) *
      ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
      Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
      ((m : ℝ) ^ 2 / d * (1 / κ ^ 2 + (d : ℝ) / (m * κ))) ≤
      (9 / 8 * g * m) * (20 / 13 * B) *
      (19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2))) *
      ((m : ℝ) ^ 2 / d * (101 / 100 * (1 / (H / (1 + g / 2)) ^ 2))) := by
    gcongr
  have heq : (9 / 8 * g * (m : ℝ)) * (20 / 13 * B) *
      (19 / 10 * (d : ℝ) ^ (1 / (1 + g / 2))) *
      ((m : ℝ) ^ 2 / d * (101 / 100 * (1 / (H / (1 + g / 2)) ^ 2))) =
      ((9 / 8 : ℝ) * (20 / 13) * (101 / 100) * (19 / 10)) *
      (g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        ((d : ℝ) ^ (1 / (1 + g / 2)) / d)) := by
    field_simp
  rw [heq, band_rpow_div_order g d hg (by omega)] at hupper
  have hconst := mul_le_mul_of_nonneg_right improved_rank_constant_lt.le
    (by positivity : 0 ≤ g * (1 + g / 2) ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
      (d : ℝ) ^ (-g / (2 + g)))
  exact (hbase.trans hupper).trans (by convert hconst using 1; ring)

/-- The prescribed parameter budget satisfies the normalized bound conditional on band counting.
The support lower bound is the sole counting premise; the window threshold is explicit. -/
theorem asymmetricBandLocalBudget_le_normalized_of_band_card_lower
    (g : ℝ) (d : ℕ) (hg : 0 ≤ g) (hg' : g ≤ 1) (hd : 1000 ≤ d) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let a := 1 + g / 2
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
    let B := (asymmetricBandTuples d W Cmin Cmax).card
    80 ≤ g * m →
    13 / 20 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤ B →
    (asymmetricBandLocalBudget d m W Be : ℝ) ≤
      10 / 3 * g * a ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  dsimp only
  let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
  let a := 1 + g / 2
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
  let B := (asymmetricBandTuples d W Cmin Cmax).card
  intro hgm hcount
  have hH : 0 < H := band_harmonic_sum_pos (d - 1) (by omega)
  have hHlog : H ≤ Real.log d + 3 / 5 := by
    dsimp [H]
    rw [band_harmonic_sum_eq]
    exact band_harmonic_pred_le_log d (by omega)
  obtain ⟨hm, hW, hκ, hlo, hhi, he, herr, hrec⟩ :=
    band_prescribed_kappa_bounds g H d hg hH hd
  have hBe : (Be : ℝ) ≤ 9 / 8 * g * m := band_errorWindow_le g m hg hg' hgm
  have hvolume : (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      20 / 13 * (B : ℝ) := by
    change 13 / 20 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤
      (B : ℝ) at hcount
    linarith
  have hexp := band_exp_le_rpow g H
    ((((d - 1 : ℕ) : ℝ) * m / W) * (1 + (d.choose 2 : ℝ) / m)) d
    hg (by omega) hHlog he
  exact asymmetricBandLocalBudget_le_normalized_of_scalar_bounds g H B d m W Be
    hg hH (Nat.cast_nonneg B) (by omega) hm hW hBe hvolume hexp hrec

/-- The actual local constraint rank has the normalized bound, conditional on band counting.
This applies at any center and received value over any field. -/
theorem finrank_asymmetricBandLocalConstraint_le_normalized_of_band_card_lower
    {F : Type*} [Field F] (g : ℝ) (d D : ℕ) (center received : F)
    (hg : 0 ≤ g) (hg' : g ≤ 1) (hd : 1000 ≤ d) (hD : 0 < D) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let a := 1 + g / 2
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let B := (asymmetricBandTuples d W Cmin Cmax).card
    80 ≤ g * m →
    13 / 20 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤ B →
    (Module.finrank F (LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := (m : ℝ) * D * (1 + g))
        hD center received)) : ℝ) ≤
      10 / 3 * g * a ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  dsimp only
  let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  intro hgm hcount
  have hbudget := asymmetricBandLocalBudget_le_normalized_of_band_card_lower
    g d hg hg' hd hgm hcount
  have hrank := finrank_asymmetricBandLocalConstraint_le
    (d := d) (m := m) (W := W) (Cmin := Cmin) (Cmax := Cmax)
    (L := (m : ℝ) * D * (1 + g)) (by omega) hD center received
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have heq : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by field_simp
  rw [heq] at hrank
  exact (Nat.cast_le.mpr hrank).trans hbudget

/-- The finite tail margins imply the sharper rank bound for the actual local constraint.
No separate band-cardinality assumption is needed; the uniform numerical margins remain explicit. -/
theorem finrank_asymmetricBandLocalConstraint_le_normalized_of_tail_margins
    {F : Type*} [Field F] (g : ℝ) (d D : ℕ) (center received : F)
    (hg : 0 ≤ g) (hg' : g ≤ 1) (hd : 1000 ≤ d) (hD : 0 < D) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let a := 1 + g / 2
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let B := (asymmetricBandTuples d W Cmin Cmax).card
    80 ≤ g * m →
    11 ≤ ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W Cmin →
    ((d - 1 : ℕ) : ℝ) * simplexTailRatio (d - 1) W (Cmax + 1) ≤ 13 / 50 →
    (Module.finrank F (LinearMap.range
      (asymmetricBandLocalConstraint (d := d) (m := m) (W := W)
        (Cmin := Cmin) (Cmax := Cmax) (L := (m : ℝ) * D * (1 + g))
        hD center received)) : ℝ) ≤
      10 / 3 * g * a ^ 2 / H ^ 2 * B * (m : ℝ) ^ 3 *
        (d : ℝ) ^ (-g / (2 + g)) := by
  dsimp only
  intro hgm hlower hupper
  apply finrank_asymmetricBandLocalConstraint_le_normalized_of_band_card_lower
    g d D center received hg hg' hd hD hgm
  simpa only [mul_div_assoc] using
    asymmetricBand_card_lower_of_tail_margins (d := d) hlower hupper

end ReedSolomon.HiddenDerivative.SharperBand
