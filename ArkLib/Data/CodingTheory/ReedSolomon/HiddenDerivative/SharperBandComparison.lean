/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors

Adapts the scalar assembly in Quang Dao's BandParameterAssembly.lean.
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandDimensionBound
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandInterpolation
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandNormalizedRank

/-!
# Interpolation with the sharper dimension and mass bounds

The improved dimension denominator `140` and normalized rank coefficient `10/3` give the
sufficient scalar threshold `1400/3`. The comparison below is on the exact integer counts
consumed by the construction and root-count frontends. The band mass and scalar endpoint
remain explicit hypotheses; there is no assumption that a fractional dimension is attained.
-/

namespace ReedSolomon.HiddenDerivative.SharperBand

open ReedSolomon.HiddenDerivative
open scoped BigOperators

/-- The improved endpoint is sufficient for strict rank-versus-dimension separation.
All divided quantities have explicit positivity hypotheses. -/
theorem band_scalar_comparison_div_140 (g H B m n D p : ℝ)
    (hg : 0 < g) (hH : 0 < H) (hB : 0 < B) (hm : 0 < m) (hn : 0 < n)
    (hp : 0 < p)
    (hendpoint : 1400 / 3 < p * H ^ 2 * (D / n) * g ^ 2 / (1 + g / 2) ^ 2) :
    n * (10 / 3 * g * (1 + g / 2) ^ 2 / H ^ 2 * B * m ^ 3 / p) <
      B * D * m ^ 3 * g ^ 3 / 140 := by
  have ha : 0 < 1 + g / 2 := by linarith
  have hid : p * H ^ 2 * (D / n) * g ^ 2 / (1 + g / 2) ^ 2 =
      (p * H ^ 2 * D * g ^ 2) / (n * (1 + g / 2) ^ 2) := by field_simp
  rw [hid] at hendpoint
  have hcross := (lt_div_iff₀ (by positivity : 0 < n * (1 + g / 2) ^ 2)).mp hendpoint
  field_simp
  nlinarith only [hcross]

/-- The sharper mass and endpoint give a strict comparison of the actual integer budgets.
The derivative order is free, so this interface can be reused with subsequent endpoint constants. -/
theorem band_budget_lt_dimensionCount_of_mass_and_endpoint
    (g : ℝ) (d D n : ℕ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hd : 1000 ≤ d) (hD : 0 < D) (hn : 0 < n) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
    100 * ((d : ℝ) + 1) ≤ g * m →
    13 / 20 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤
      (asymmetricBandTuples d W Cmin Cmax).card →
    1400 / 3 < (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * ((D : ℝ) / n) * g ^ 2 /
      (1 + g / 2) ^ 2 →
    n * asymmetricBandLocalBudget d m W Be <
      asymmetricBandDimensionCount D d m W Cmin Cmax ((D : ℝ) * m * (1 + g)) := by
  dsimp only
  let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
  let B := (asymmetricBandTuples d W Cmin Cmax).card
  intro hgm hmass hendpoint
  have hH : 0 < H := band_harmonic_sum_pos _ (by omega)
  obtain ⟨hm, hW, hκ, hlo, hhi, he, herr, hrec⟩ :=
    band_prescribed_kappa_bounds g H d hg.le hH hd
  have hB : (0 : ℝ) < B :=
    (by positivity : (0 : ℝ) < 13 / 20 *
      ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2)).trans_le hmass
  have hgm' : 80 ≤ g * m := by
    have hdp : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hbudget := asymmetricBandLocalBudget_le_normalized_of_band_card_lower
    g d hg.le hg1 hd hgm' hmass
  have hdim := finrank_asymmetricBandSpace_ge_prescribed_cubic_div_140
    (F := ℚ) (d := d) (m := m) (W := W) (Cmin := Cmin) hd hD hg.le hg1 hgm
  rw [finrank_asymmetricBandSpace_eq_dimensionCount (by omega) hD] at hdim
  have hdp : (0 : ℝ) < d := by positivity
  have hstrict := band_scalar_comparison_div_140 g H B m n D ((d : ℝ) ^ (g / (2 + g)))
    hg hH hB (by positivity) (by positivity) (Real.rpow_pos_of_pos hdp _) hendpoint
  have hpow : (d : ℝ) ^ (-g / (2 + g)) = 1 / (d : ℝ) ^ (g / (2 + g)) := by
    rw [neg_div, Real.rpow_neg hdp.le]
    simp only [one_div]
  rw [hpow, mul_one_div] at hbudget
  have htotal := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  have hfinal := (htotal.trans_lt hstrict).trans_le hdim
  change n * asymmetricBandLocalBudget d m W Be <
    asymmetricBandDimensionCount D d m W Cmin Cmax ((D : ℝ) * m * (1 + g))
  apply (Nat.cast_lt (α := ℝ)).mp
  rw [Nat.cast_mul]
  exact hfinal

/-- The sharpened comparison yields an actual nonzero interpolant at every received word.
This is the existing band-space construction, with the improved numerical hypotheses. -/
theorem exists_nonzero_band_interpolant_of_mass_and_endpoint
    {F : Type*} [Field F] (g : ℝ) (d D n : ℕ) (centers received : Fin n → F)
    (hg : 0 < g) (hg1 : g ≤ 1) (hd : 1000 ≤ d) (hD : 0 < D) (hn : 0 < n) :
    let H := ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let L := (D : ℝ) * m * (1 + g)
    100 * ((d : ℝ) + 1) ≤ g * m →
    13 / 20 * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ≤
      (asymmetricBandTuples d W Cmin Cmax).card →
    1400 / 3 < (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * ((D : ℝ) / n) * g ^ 2 /
      (1 + g / 2) ^ 2 →
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ asymmetricBandSpace F D d m W Cmin Cmax L hD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  dsimp only
  intro hgm hmass hendpoint
  have h := band_budget_lt_dimensionCount_of_mass_and_endpoint
    g d D n hg hg1 hd hD hn hgm hmass hendpoint
  apply exists_nonzero_band_interpolant (by omega) hD centers received
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have heq : ∀ m : ℕ, (D : ℝ) * m * (1 + g) / D = m * (1 + g) := by
    intro m
    field_simp
  simpa only [Fintype.card_fin, heq] using h

end ReedSolomon.HiddenDerivative.SharperBand
