/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexBandParameters
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexMaximumTail
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexTailBounds
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.TunableBandEndpoint

/-!
# Uniform discrete band mass at the improved derivative order

The exact simplex second-moment bound gives mass `13/20` whenever `log d ≥ 22` and
`g H / (1 + g/2) ≥ 11/2`. The lower tail is feasible; the upper estimate remains valid
even when its threshold exceeds the entire simplex budget. All floor and ceiling errors
are retained. These hypotheses hold at order `ceil(exp((11/2)/δ))` in the all-rate frontend.
-/

namespace ReedSolomon.HiddenDerivative

/-- Uniform mass for the prescribed discrete band, with explicit scalar prerequisites. -/
theorem asymmetricBand_mass_of_simplex_parameters (g : ℝ) (d m : ℕ)
    (hd : 1000 ≤ d) (hlog : 22 ≤ Real.log d) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hgap : 11 / 2 ≤ g * (harmonic (d - 1) : ℝ) / (1 + g / 2))
    (hsize : 100 * (d : ℝ) ^ 2 * (harmonic (d - 1) : ℝ) ≤ m) :
    let H := (harmonic (d - 1) : ℝ)
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    (13 / 20 : ℝ) * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
      (asymmetricBandTuples d W Cmin Cmax).card := by
  let H := (harmonic (d - 1) : ℝ)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  let z := (Cmin : ℝ) / ((W : ℝ) + 1)
  obtain ⟨hH, hsmall, hhlo, hhhi⟩ := band_harmonic_simplex_errors d hd hlog
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hscale := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 100 * (d : ℝ) ^ 2)
  have hmD : (d : ℝ) ≤ m := by nlinarith only [hdR, hscale, hsize]
  have hm : 0 < m := by exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hmsmall : 1000 * H ^ 2 ≤ m := hsmall.trans hmD
  have hr : 0 < d - 1 := by omega
  have hrR : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast hr
  obtain ⟨ht, hlower⟩ := band_simplex_lower_exponent g H d m
    hd hH hg hg1 hsmall hm hgap hhhi
  have hupper := band_simplex_upper_exponent g H d m
    hd hH hg hsmall hmsmall hgap hhlo
  apply asymmetricBand_card_lower_of_tighter_tail_margins
  · calc
      (14 : ℝ) ≤ Real.exp (269 / 100) := band_lower_tail_exp_margin_div_140.le
      _ ≤ Real.exp (Real.log (d - 1 : ℕ) + -((d - 1 : ℕ) : ℝ) * z / (1 - z)) := by
        apply Real.exp_le_exp.mpr
        change 269 / 100 ≤ Real.log (d - 1 : ℕ) -
          ((d - 1 : ℕ) : ℝ) * z / (1 - z) at hlower
        simpa only [neg_mul, neg_div, sub_eq_add_neg] using hlower
      _ = ((d - 1 : ℕ) : ℝ) * Real.exp (-((d - 1 : ℕ) : ℝ) * z / (1 - z)) := by
        rw [Real.exp_add, Real.exp_log hrR]
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_lower_le_simplexTailRatio ht) hrR.le
  · calc
      _ ≤ ((d - 1 : ℕ) : ℝ) * Real.exp (-((d - 1 : ℕ) : ℝ) * (Cmax + 1 : ℕ) /
          ((W : ℝ) + (d - 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left (simplexTailRatio_le_exp_upper _ _ _ hr) hrR.le
      _ = Real.exp (Real.log (d - 1 : ℕ) + -((d - 1 : ℕ) : ℝ) * (Cmax + 1 : ℕ) /
          ((W : ℝ) + (d - 1 : ℕ))) := by rw [Real.exp_add, Real.exp_log hrR]
      _ ≤ Real.exp (-(263 / 200)) := by
        apply Real.exp_le_exp.mpr
        change Real.log (d - 1 : ℕ) - ((d - 1 : ℕ) : ℝ) * (Cmax + 1 : ℕ) /
          ((W : ℝ) + (d - 1 : ℕ)) ≤ -(263 / 200) at hupper
        simpa only [neg_mul, neg_div, sub_eq_add_neg] using hupper
      _ ≤ 27 / 100 := by
        rw [Real.exp_neg, ← one_div]
        apply (div_le_iff₀ (Real.exp_pos _)).mpr
        have := band_upper_tail_exp_margin_div_140
        linarith

end ReedSolomon.HiddenDerivative
