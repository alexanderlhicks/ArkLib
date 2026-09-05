/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors

Generalizes the endpoint argument in Quang Dao's BandEndpointComparison.lean.
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.BandEndpointComparison

/-!
# Endpoint estimates with a tunable derivative-order constant

The same finite endpoint argument works for every `c ≥ 4`. Keeping `c` explicit avoids
repeating the parameter proof at each improved dimension or mass constant. In particular,
`c = 11/2` exceeds the threshold `1400/3` coming from dimension denominator `140` and
rank coefficient `10/3`. This is a scalar theorem, not a completed list-decoding theorem:
the stronger band count at the prescribed parameters remains a separate obligation.
-/

namespace ReedSolomon.HiddenDerivative

/-- The upper endpoint dominates its zero-gap limit, uniformly in the constant. -/
theorem band_endpoint_at_upper_of_constant (c δ : ℝ) (hc : 2 ≤ c)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    c ^ 2 * Real.exp (c / 2) ≤
      4 * c ^ 2 * (1 - δ) / (2 - δ) ^ 2 * Real.exp (c / (2 - δ)) := by
  let t := δ / (2 - δ)
  have hden : 0 < 2 - δ := by linarith
  have ht : 0 ≤ t := div_nonneg hδ.le hden.le
  have ht' : t ≤ 1 / 7 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hpref : 4 * (1 - δ) / (2 - δ) ^ 2 = 1 - t ^ 2 := by
    dsimp [t]
    field_simp
    ring
  have hexponent : c / (2 - δ) = c / 2 + c / 2 * t := by
    dsimp [t]
    field_simp
    ring
  have ht2 : t ^ 2 ≤ 1 / 49 := by nlinarith
  have hp : 0 ≤ 1 - t ^ 2 := by linarith
  have haux : 0 ≤ c / 2 * (1 - t ^ 2) - t := by
    have h := mul_le_mul_of_nonneg_right hc hp
    nlinarith
  have hpoly : 1 ≤ (1 - t ^ 2) * (1 + c / 2 * t) := by
    have h := mul_nonneg ht haux
    nlinarith
  have hlin := Real.add_one_le_exp (c / 2 * t)
  have hgain : 1 ≤ (1 - t ^ 2) * Real.exp (c / 2 * t) := by
    have h := mul_le_mul_of_nonneg_left hlin hp
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hgain
    (by positivity : 0 ≤ c ^ 2 * Real.exp (c / 2))
  rw [hexponent, Real.exp_add]
  have heq : 4 * c ^ 2 * (1 - δ) / (2 - δ) ^ 2 = c ^ 2 * (1 - t ^ 2) := by
    rw [← hpref]
    ring
  rw [heq]
  nlinarith only [hscale]

/-- The high-rate scalar expression is bounded below by `c² exp(c/2)`. -/
theorem band_high_rate_scalar_lower (c δ ρ H ℓ : ℝ) (hc : 2 ≤ c)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ ≤ ρ) (hρ' : ρ ≤ 1 - δ)
    (hH : c / δ ≤ H) (hℓ : c / δ ≤ ℓ) :
    c ^ 2 * Real.exp (c / 2) ≤ Real.exp (ℓ * (δ / ρ) / (2 + δ / ρ)) *
      H ^ 2 * ρ * (δ / ρ) ^ 2 / (1 + (δ / ρ) / 2) ^ 2 := by
  have hcp : 0 < c := by linarith
  have hρp : 0 < ρ := hδ.trans_le hρ
  have hHp : 0 < H := (div_pos hcp hδ).trans_le hH
  have hden : 0 < 2 + δ / ρ := by positivity
  have he : c / (2 * ρ + δ) ≤ ℓ * (δ / ρ) / (2 + δ / ρ) := by
    have h := mul_le_mul_of_nonneg_right hℓ (by positivity : 0 ≤ δ / ρ)
    have h' := div_le_div_of_nonneg_right h hden.le
    have hid : (c / δ) * (δ / ρ) / (2 + δ / ρ) = c / (2 * ρ + δ) := by
      field_simp
    rwa [hid] at h'
  have he' := Real.exp_le_exp.mpr he
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ c / δ) hH 2
  have hbound : Real.exp (c / (2 * ρ + δ)) * (c / δ) ^ 2 * ρ * (δ / ρ) ^ 2 /
      (1 + (δ / ρ) / 2) ^ 2 ≤
      Real.exp (ℓ * (δ / ρ) / (2 + δ / ρ)) * H ^ 2 * ρ * (δ / ρ) ^ 2 /
      (1 + (δ / ρ) / 2) ^ 2 := by gcongr
  have hid : Real.exp (c / (2 * ρ + δ)) * (c / δ) ^ 2 * ρ * (δ / ρ) ^ 2 /
      (1 + (δ / ρ) / 2) ^ 2 =
      4 * c ^ 2 * ρ / (2 * ρ + δ) ^ 2 * Real.exp (c / (2 * ρ + δ)) := by
    field_simp
    ring
  rw [hid] at hbound
  have hmono := band_endpoint_function_antitone δ ρ (1 - δ) c hδ hρ hρ' hcp.le
  have heq : 2 * (1 - δ) + δ = 2 - δ := by ring
  rw [heq] at hmono
  exact ((band_endpoint_at_upper_of_constant c δ hc hδ hδ').trans hmono).trans hbound

/-- The low-rate expression has the same lower bound, without another numerical certificate. -/
theorem band_low_rate_scalar_lower (c δ ρ H ℓ : ℝ) (hc : 2 ≤ c)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ)
    (hH : c / δ ≤ H) (hℓ : c / δ ≤ ℓ) :
    c ^ 2 * Real.exp (c / 2) ≤ Real.exp (ℓ / 3) * H ^ 2 * ρ / (3 / 2) ^ 2 := by
  have hcp : 0 < c := by linarith
  have hHp : 0 < H := (div_pos hcp hδ).trans_le hH
  have hρp : 0 < ρ := (by positivity : 0 < δ / 3).trans_le hρ
  have hlow : 4 * c ≤ c / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have he : c / 2 + 1 ≤ ℓ / 3 := by linarith
  have he' := Real.exp_le_exp.mpr he
  have hfactor : (4 * c ^ 2 / 27) / δ ≤ H ^ 2 * ρ / (3 / 2) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ c / δ) hH 2
    have hmul := mul_le_mul hsq hρ (by positivity : 0 ≤ δ / 3) (sq_nonneg H)
    have hid : (c / δ) ^ 2 * (δ / 3) / (3 / 2) ^ 2 = (4 * c ^ 2 / 27) / δ := by
      field_simp
      ring
    rw [← hid]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hfactor' : 16 * c ^ 2 / 27 ≤ H ^ 2 * ρ / (3 / 2) ^ 2 := by
    apply le_trans ?_ hfactor
    apply (le_div_iff₀ hδ).mpr
    nlinarith [sq_nonneg c]
  have hbound := mul_le_mul he' hfactor' (by positivity) (Real.exp_pos _).le
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hgain : c ^ 2 * Real.exp (c / 2) ≤ Real.exp (c / 2 + 1) * (16 * c ^ 2 / 27) := by
    rw [Real.exp_add]
    have h := mul_le_mul_of_nonneg_left htwo
      (by positivity : 0 ≤ Real.exp (c / 2) * (16 * c ^ 2 / 27))
    nlinarith [Real.exp_pos (c / 2), sq_nonneg c]
  exact hgain.trans (by convert hbound using 1; ring)

/-- The rounded order has the logarithmic and harmonic lower bounds for every `c ≥ 4`. -/
theorem band_order_lower_of_constant (c δ : ℝ) (hc : 4 ≤ c)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    let d := Nat.ceil (Real.exp (c / δ))
    1000 ≤ d ∧ c / δ ≤ Real.log d ∧ c / δ ≤ (harmonic (d - 1) : ℝ) := by
  let d := Nat.ceil (Real.exp (c / δ))
  have hceil : Real.exp (c / δ) ≤ (d : ℝ) := Nat.le_ceil _
  have hlog := Real.log_le_log (Real.exp_pos _) hceil
  rw [Real.log_exp] at hlog
  have he : (7 : ℝ) ≤ c / δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hnum : (1000 : ℝ) < Real.exp 7 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7) 15
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hd : 1000 ≤ d := by
    exact_mod_cast (hnum.trans_le ((Real.exp_le_exp.mpr he).trans hceil)).le
  have hh := log_add_one_le_harmonic (d - 1)
  have heq : d - 1 + 1 = d := by omega
  rw [heq] at hh
  exact ⟨hd, hlog, hlog.trans hh⟩

/-- A single scalar constant controls both rate regimes at the rounded derivative order. -/
theorem band_prescribed_endpoint_lower_of_constant (c δ ρ : ℝ) (hc : 4 ≤ c)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp (c / δ))
    let H := (harmonic (d - 1) : ℝ)
    let g := min 1 (δ / ρ)
    c ^ 2 * Real.exp (c / 2) ≤
      (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * ρ * g ^ 2 / (1 + g / 2) ^ 2 := by
  let d := Nat.ceil (Real.exp (c / δ))
  have hρp : 0 < ρ := (by positivity : 0 < δ / 3).trans_le hρ
  obtain ⟨hd, hlog, hH⟩ := band_order_lower_of_constant c δ hc hδ hδ'
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  dsimp only
  rw [Real.rpow_def_of_pos hdp]
  by_cases hhigh : δ ≤ ρ
  · have hg : min (1 : ℝ) (δ / ρ) = δ / ρ :=
      min_eq_right ((div_le_one hρp).mpr hhigh)
    rw [hg]
    have h := band_high_rate_scalar_lower c δ ρ (harmonic (d - 1)) (Real.log d)
      (by linarith) hδ hδ' hhigh hρ' hH hlog
    dsimp [d] at h ⊢
    convert h using 1; ring_nf
  · have hg : min (1 : ℝ) (δ / ρ) = 1 :=
      min_eq_left ((one_le_div hρp).mpr (by linarith))
    rw [hg]
    have h := band_low_rate_scalar_lower c δ ρ (harmonic (d - 1)) (Real.log d)
      (by linarith) hδ hδ' hρ hH hlog
    dsimp [d] at h ⊢
    convert h using 1; ring_nf

/-- A rational exponential partial sum certifies the `11/2` candidate against `/140`. -/
theorem band_endpoint_constant_div_140_gt :
    (1400 / 3 : ℝ) < (11 / 2) ^ 2 * Real.exp (11 / 4) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 4) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The `11/2` order satisfies the improved scalar comparison at every admissible rate. -/
theorem band_prescribed_endpoint_div_140_gt (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp ((11 / 2) / δ))
    let H := (harmonic (d - 1) : ℝ)
    let g := min 1 (δ / ρ)
    (1400 / 3 : ℝ) <
      (d : ℝ) ^ (g / (2 + g)) * H ^ 2 * ρ * g ^ 2 / (1 + g / 2) ^ 2 := by
  have h := band_prescribed_endpoint_lower_of_constant
    (11 / 2) δ ρ (by norm_num) hδ hδ' hρ hρ'
  dsimp only at h ⊢
  rw [show (11 / 2 : ℝ) / 2 = 11 / 4 by norm_num] at h
  exact band_endpoint_constant_div_140_gt.trans_le h

/-- The same prescribed multiplicity supplies the discrete rounding budget for any `c ≥ 4`. -/
theorem band_gap_multiplicity_of_constant (c δ ρ : ℝ) (hc : 4 ≤ c)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp (c / δ))
    let H := (harmonic (d - 1) : ℝ)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let g := min 1 (δ / ρ)
    100 * ((d : ℝ) + 1) ≤ g * m := by
  let d := Nat.ceil (Real.exp (c / δ))
  let H := (harmonic (d - 1) : ℝ)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  obtain ⟨hd, hlog, hH⟩ := band_order_lower_of_constant c δ hc hδ hδ'
  have hd' : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hδH : c ≤ δ * H := by
    have h := (div_le_iff₀ hδ).mp hH
    nlinarith
  have hg : δ ≤ min 1 (δ / ρ) := by
    apply le_min (by linarith)
    apply (le_div_iff₀ hρ).mpr
    nlinarith
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hscaled := mul_le_mul_of_nonneg_left hsize hδ.le
  have hscaledH := mul_le_mul_of_nonneg_left hδH
    (by positivity : 0 ≤ 100 * (d : ℝ) ^ 2)
  have hgscaled := mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg m)
  have hpoly : 100 * ((d : ℝ) + 1) ≤ 100 * (d : ℝ) ^ 2 * c := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg (d : ℝ))
    nlinarith
  dsimp only
  change 100 * ((d : ℝ) + 1) ≤ min 1 (δ / ρ) * m
  nlinarith only [hscaled, hscaledH, hgscaled, hpoly]

/-- The tighter harmonic bound permits a lower-tail first moment of at least `14` at `c=11/2`.
This certifies only the exponential margin, not its finite-parameter substitution. -/
theorem band_lower_tail_exp_margin_div_140 : (14 : ℝ) < Real.exp (269 / 100) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 269 / 100) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The corresponding upper-tail exponential certificate allows union bound `27/100`. -/
theorem band_upper_tail_exp_margin_div_140 : (100 / 27 : ℝ) < Real.exp (263 / 200) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 263 / 200) 10
  norm_num [Finset.sum_range_succ] at h
  linarith

end ReedSolomon.HiddenDerivative
