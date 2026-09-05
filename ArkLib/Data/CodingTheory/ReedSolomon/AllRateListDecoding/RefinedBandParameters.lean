/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors

Adapts Quang Dao's parameter assembly to the sharper discrete band bounds.
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.BandParameterAssembly
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SimplexBandMass
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.SharperBandComparison

/-!
# Prescribed all-rate parameters with derivative-order constant `5.5`

The discrete simplex mass, dimension denominator `140`, and scalar endpoint now combine
without a residual counting hypothesis. The block threshold remains `8m`; the ambient
dimension is the same as in the original construction. The original `6.76` interfaces remain
unchanged, so callers can explicitly choose the improved theorem.
-/

namespace ReedSolomon.AllRateListDecoding

noncomputable section

open HiddenDerivative

/-- The improved derivative order, retaining the separate order-zero large-gap regime. -/
def refinedDerivativeOrder (delta : ℝ) : ℕ :=
  if (1 / 4 : ℝ) ≤ delta then 0 else Nat.ceil (Real.exp ((11 / 2) / delta))

@[simp]
theorem refinedDerivativeOrder_eq_zero {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta) :
    refinedDerivativeOrder delta = 0 := by
  rw [refinedDerivativeOrder, if_pos hdelta]

/-- Below one quarter the improved order is exactly the rounded exponential. -/
theorem refinedDerivativeOrder_eq_ceil {delta : ℝ} (hdelta : delta < (1 / 4 : ℝ)) :
    refinedDerivativeOrder delta = Nat.ceil (Real.exp ((11 / 2) / delta)) := by
  rw [refinedDerivativeOrder, if_neg (not_le_of_gt hdelta)]

/-- The same quadratic multiplicity formula, evaluated at the improved derivative order. -/
def refinedBandMultiplicity (delta : ℝ) : ℕ :=
  Nat.ceil (100 * (refinedDerivativeOrder delta : ℝ) ^ 2 *
    harmonicNumber (refinedDerivativeOrder delta - 1))

/-- The improved rounded order never exceeds the original `6.76` order at a positive gap. -/
theorem refinedDerivativeOrder_le_strong {δ : ℝ} (hδ : 0 < δ) :
    refinedDerivativeOrder δ ≤ strongDerivativeOrder δ := by
  by_cases hquarter : (1 / 4 : ℝ) ≤ δ
  · simp only [refinedDerivativeOrder_eq_zero hquarter, strongDerivativeOrder_eq_zero hquarter,
      le_refl]
  · rw [refinedDerivativeOrder_eq_ceil (lt_of_not_ge hquarter),
      strongDerivativeOrder_eq_ceil (lt_of_not_ge hquarter)]
    apply Nat.ceil_mono
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by norm_num) hδ.le

/-- The multiplicity and hence the required block threshold also do not increase. -/
theorem refinedBandMultiplicity_le_strong {δ : ℝ} (hδ : 0 < δ) :
    refinedBandMultiplicity δ ≤ strongBandMultiplicity δ := by
  have hd := refinedDerivativeOrder_le_strong hδ
  have hH : harmonicNumber (refinedDerivativeOrder δ - 1) ≤
      harmonicNumber (strongDerivativeOrder δ - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le_sub_right hd 1))
    intro i _ _
    positivity
  apply Nat.ceil_mono
  refine mul_le_mul ?_ hH ?_ ?_
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hd) 2) (by norm_num)
  · unfold harmonicNumber
    positivity
  · positivity

/-- Ambient room follows uniformly for any derivative-order constant at least four. -/
theorem band_block_size_bounds_of_constant (c δ : ℝ) (n k : ℕ) (hc : 4 ≤ c)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp (c / δ)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp (c / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := Nat.ceil (Real.exp (c / δ))
    let D := strongBandAmbientDimension δ n k - 1
    12 ≤ δ * n ∧ 0 < D ∧ d < D ∧ δ / 3 ≤ (D : ℝ) / n ∧
      (D : ℝ) / n ≤ 1 - δ := by
  let d := Nat.ceil (Real.exp (c / δ))
  let H := harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  obtain ⟨hd, _, hH⟩ := band_order_lower_of_constant c δ hc hδ hδ'.le
  have hδH : 4 ≤ δ * H := by
    dsimp [H]
    rw [harmonicNumber_eq_harmonic]
    have := (div_le_iff₀ hδ).mp hH
    linarith
  have hm : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hscaled := mul_le_mul_of_nonneg_left hm hδ.le
  have hscaledH := mul_le_mul_of_nonneg_left hδH
    (by positivity : 0 ≤ 100 * (d : ℝ) ^ 2)
  have hblock' : 8 * m ≤ n := hblock
  have hmn : 8 * (m : ℝ) ≤ n := by exact_mod_cast hblock'
  have hδmn := mul_le_mul_of_nonneg_left hmn hδ.le
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hbig : 3200 * (d : ℝ) ^ 2 ≤ δ * n := by nlinarith
  have hsize : 12 ≤ δ * n := by nlinarith
  obtain ⟨hD, hlo, hhi⟩ := strongBandAmbientRate_bounds hδ hδ' hk hsize hA
  have hn : (0 : ℝ) < n := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    rw [hz, mul_zero] at hsize
    norm_num at hsize
  have hlow := (le_div_iff₀ hn).mp hlo
  have hdD : d < strongBandAmbientDimension δ n k - 1 := by
    have : (d : ℝ) < (strongBandAmbientDimension δ n k - 1 : ℕ) := by nlinarith
    exact_mod_cast this
  exact ⟨hsize, hD, hdD, hlo, hhi⟩

/-- The prescribed `5.5` order supplies the stronger discrete band mass at every feasible rate. -/
theorem refined_band_rate_parameter_estimates (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp ((11 / 2) / δ))
    let H := harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let g := min 1 (δ / ρ)
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    1000 ≤ d ∧ 0 < H ∧ 0 < g ∧ g ≤ 1 ∧
      100 * ((d : ℝ) + 1) ≤ g * m ∧ 0 < m ∧ 0 < W ∧
      (13 / 20 : ℝ) * (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
        (asymmetricBandTuples d W ⌊(1 - g / 10) * m⌋₊
          ⌈(1 + 13 * g / 20) * m⌉₊).card := by
  let d := Nat.ceil (Real.exp ((11 / 2) / δ))
  let H := harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let g := min 1 (δ / ρ)
  obtain ⟨hd, hlog, hH⟩ := band_order_lower_of_constant (11 / 2) δ (by norm_num) hδ hδ'
  have hδH : 11 / 2 ≤ δ * H := by
    dsimp [H]
    rw [harmonicNumber_eq_harmonic]
    have := (div_le_iff₀ hδ).mp hH
    nlinarith
  have hHp : 0 < H := by nlinarith
  obtain ⟨hg, hg1, _, _, hag⟩ :=
    band_relativeSlack_bounds hδ (by linarith) hρ hρ'
  have hgap : 11 / 2 ≤ g * H / (1 + g / 2) := by
    apply hδH.trans
    apply (le_div_iff₀ (by positivity : 0 < 1 + g / 2)).mpr
    have := mul_le_mul_of_nonneg_right hag hHp.le
    nlinarith only [this]
  have hlog22 : 22 ≤ Real.log d := by
    apply le_trans _ hlog
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hgm : 100 * ((d : ℝ) + 1) ≤ g * m := by
    have h := band_gap_multiplicity_of_constant (11 / 2) δ ρ (by norm_num) hδ hδ' hρ hρ'
    dsimp [d, g, m, H]
    simpa only [harmonicNumber_eq_harmonic] using h
  obtain ⟨hm, hW, _⟩ := band_prescribed_kappa_bounds g H d hg.le hHp hd
  have hmass := asymmetricBand_mass_of_simplex_parameters g d m hd hlog22 hg.le hg1
    (by simpa only [H, harmonicNumber_eq_harmonic] using hgap)
    (by simpa only [m, H, harmonicNumber_eq_harmonic] using (Nat.le_ceil
      (100 * (d : ℝ) ^ 2 * H)))
  refine ⟨hd, hHp, hg, hg1, hgm, hm, hW, ?_⟩
  simpa only [d, m, H, g, harmonicNumber_eq_harmonic] using hmass

/-- The improved multiplicity is positive in its small-gap regime. -/
theorem refinedBandMultiplicity_pos {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    0 < refinedBandMultiplicity δ := by
  obtain ⟨_, _, _, _, _, hm, _, _⟩ :=
    refined_band_rate_parameter_estimates δ (1 - δ) hδ hδ'.le (by linarith) le_rfl
  simpa only [refinedBandMultiplicity, refinedDerivativeOrder_eq_ceil hδ'] using hm

/-- Exact integer rank-versus-dimension separation at the improved prescribed order.
No mass or endpoint inequality is left as an assumption. -/
theorem refined_band_budget_lt_dimensionCount
    (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let d := refinedDerivativeOrder δ
    let H := harmonicNumber (d - 1)
    let m := refinedBandMultiplicity δ
    let D := strongBandAmbientDimension δ n k - 1
    let g := min 1 (δ / ((D : ℝ) / n))
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
    let Be := Nat.ceil ((m : ℝ) * (1 + g) - Cmin)
    n * asymmetricBandLocalBudget d m W Be <
      asymmetricBandDimensionCount D d m W Cmin Cmax ((D : ℝ) * m * (1 + g)) := by
  let d := Nat.ceil (Real.exp ((11 / 2) / δ))
  let D := strongBandAmbientDimension δ n k - 1
  let ρ := (D : ℝ) / n
  let g := min 1 (δ / ρ)
  have hblock' : 8 * Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1)) ≤ n := by
    simpa only [refinedBandMultiplicity, refinedDerivativeOrder_eq_ceil hδ'] using hblock
  obtain ⟨_, hD, _, hρlo, hρhi⟩ :=
    band_block_size_bounds_of_constant (11 / 2) δ n k (by norm_num) hδ hδ' hk hblock' hA
  have hρ : 0 < ρ := (by positivity : 0 < δ / 3).trans_le hρlo
  obtain ⟨hd, _, hg, hg1, hgm, _, _, hmass⟩ :=
    refined_band_rate_parameter_estimates δ ρ hδ hδ'.le hρ hρhi
  have hn : 0 < n := by
    have hm := refinedBandMultiplicity_pos hδ hδ'
    omega
  have hendpoint := band_prescribed_endpoint_div_140_gt δ ρ hδ hδ'.le hρlo hρhi
  have h := SharperBand.band_budget_lt_dimensionCount_of_mass_and_endpoint
    g d D n hg hg1 hd hD hn
    (by simpa only [harmonicNumber, Nat.cast_add, Nat.cast_one, d, g, ρ] using hgm)
    (by simpa only [harmonicNumber, Nat.cast_add, Nat.cast_one, d, g, ρ,
      mul_div_assoc] using hmass)
    (by simpa only [band_harmonic_sum_eq, d, g, ρ] using hendpoint)
  simpa only [refinedBandMultiplicity, refinedDerivativeOrder_eq_ceil hδ',
    harmonicNumber, Nat.cast_add, Nat.cast_one, d, D, g, ρ] using h

end
end ReedSolomon.AllRateListDecoding
