/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.BandParameterBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Uniform finite-error estimates for the simplex band

The harmonic parameter is small compared with the derivative order once `log d ≥ 22`.
These coarse, rational bounds control the finite errors in both maximum-tail estimates.
No asymptotic approximation or numerical evaluation of a harmonic number is used.
-/

namespace ReedSolomon.HiddenDerivative

/-- A uniform exponential bound, with an exact rational Taylor certificate at the endpoint. -/
theorem band_thousand_sq_add_one_le_exp {t : ℝ} (ht : 22 ≤ t) :
    1000 * (t + 1) ^ 2 ≤ Real.exp t := by
  have hbase : (1000000 : ℝ) ≤ Real.exp 22 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 22) 12
    norm_num [Finset.sum_range_succ] at h
    linarith
  have htail := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ t - 22) 3
  norm_num [Finset.sum_range_succ] at htail
  have hprod := mul_le_mul hbase htail (by positivity : 0 ≤ 1 + (t - 22) +
    (t - 22) ^ 2 / 2) (Real.exp_pos 22).le
  have heq : Real.exp 22 * Real.exp (t - 22) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hprod
  nlinarith only [hprod, sq_nonneg (t - 22), ht]

/-- Harmonic size and the two-sided harmonic/logarithm gap needed by the finite tails. -/
theorem band_harmonic_simplex_errors (d : ℕ) (hd : 1000 ≤ d)
    (hlog : 22 ≤ Real.log d) :
    let H := (harmonic (d - 1) : ℝ)
    1 ≤ H ∧ 1000 * H ^ 2 ≤ d ∧
      1 / 2 ≤ H - Real.log (d - 1 : ℕ) ∧
      H - Real.log (d - 1 : ℕ) ≤ 3 / 5 := by
  let H := (harmonic (d - 1) : ℝ)
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlo := log_add_one_le_harmonic (d - 1)
  rw [show d - 1 + 1 = d by omega] at hlo
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hhi := band_harmonic_pred_le_log d (by omega)
  have hsq : H ^ 2 ≤ (Real.log d + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by dsimp [H]; linarith) 2
  have he := band_thousand_sq_add_one_le_exp hlog
  rw [Real.exp_log hdp] at he
  have hsmall : 1000 * H ^ 2 ≤ d := by linarith
  have hlower := Real.one_half_lt_eulerMascheroniConstant.trans
    (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (d - 1))
  simp only [Real.eulerMascheroniSeq', show d - 1 ≠ 0 by omega, ↓reduceIte] at hlower
  have hupper := band_harmonic_le_log (d - 1) (by omega)
  exact ⟨hH, hsmall, hlower.le, by linarith⟩

/-- The lower threshold is feasible, and its finite exponential error costs at most `1/100`.
The statement retains the exact floor in the width and in the threshold. -/
theorem band_simplex_lower_exponent (g H : ℝ) (d m : ℕ)
    (hd : 1000 ≤ d) (hH : 1 ≤ H) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hsmall : 1000 * H ^ 2 ≤ d) (hm : 0 < m)
    (hgap : 11 / 2 ≤ g * H / (1 + g / 2))
    (hharm : H - Real.log (d - 1 : ℕ) ≤ 3 / 5) :
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let t := Nat.floor ((1 - g / 10) * m)
    let z := (t : ℝ) / ((W : ℝ) + 1)
    t ≤ W ∧ 269 / 100 ≤ Real.log (d - 1 : ℕ) -
      ((d - 1 : ℕ) : ℝ) * z / (1 - z) := by
  let a := 1 + g / 2
  let b := 1 - g / 10
  let W := Nat.floor (a * d * m / H)
  let t := Nat.floor (b * m)
  let z := (t : ℝ) / ((W : ℝ) + 1)
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hHp : 0 < H := by linarith
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (W : ℝ) + 1 := by positivity
  have hR : 0 < a * d * m / H := by positivity
  have hf : a * d * m / H ≤ (W : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have ht : (t : ℝ) ≤ b * m := Nat.floor_le (mul_nonneg hb hmp.le)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz : z ≤ b * H / (a * d) := by
    calc
      z ≤ b * m / ((W : ℝ) + 1) := div_le_div_of_nonneg_right ht hden.le
      _ ≤ b * m / (a * d * m / H) :=
        div_le_div_of_nonneg_left (by positivity) hR hf
      _ = b * H / (a * d) := by field_simp
  have hzH : z ≤ H / d := by
    apply hz.trans
    apply (div_le_div_iff₀ (by positivity : 0 < a * d) hdp).mpr
    have hab : b ≤ a := hb1.trans ha
    nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (mul_nonneg hHp.le hdp.le)]
  have hlinear : 1000 * H ≤ d := by nlinarith only [hH, hsmall]
  have hzsmall : z ≤ 1 / 1000 := hzH.trans ((div_le_iff₀ hdp).mpr (by linarith))
  have hz1 : z < 1 := by linarith
  have htW : t ≤ W := by
    have hlt : (t : ℝ) < (W : ℝ) + 1 := (div_lt_one hden).mp hz1
    have hlt' : (t : ℝ) < (W + 1 : ℕ) := by simpa only [Nat.cast_add,
      Nat.cast_one] using hlt
    exact Nat.le_of_lt_succ (Nat.cast_lt.mp hlt')
  have hr : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hrz : ((d - 1 : ℕ) : ℝ) * z ≤ b * H / a := by
    calc
      _ ≤ (d : ℝ) * z := mul_le_mul_of_nonneg_right hr hz0
      _ ≤ (d : ℝ) * (b * H / (a * d)) := mul_le_mul_of_nonneg_left hz hdp.le
      _ = b * H / a := by field_simp
  have hzsq := pow_le_pow_left₀ hz0 hzH 2
  have hquad : ((d - 1 : ℕ) : ℝ) * z ^ 2 ≤ 1 / 1000 := by
    calc
      _ ≤ (d : ℝ) * z ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg z)
      _ ≤ (d : ℝ) * (H / d) ^ 2 := mul_le_mul_of_nonneg_left hzsq hdp.le
      _ = H ^ 2 / d := by field_simp
      _ ≤ 1 / 1000 := (div_le_iff₀ hdp).mpr (by linarith)
  have herr : ((d - 1 : ℕ) : ℝ) * z ^ 2 / (1 - z) ≤ 1 / 100 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - z)).mpr
    linarith
  have hid : ((d - 1 : ℕ) : ℝ) * z / (1 - z) =
      ((d - 1 : ℕ) : ℝ) * z + ((d - 1 : ℕ) : ℝ) * z ^ 2 / (1 - z) := by
    field_simp [ne_of_gt (sub_pos.mpr hz1)]
    ring
  have hbg : b * H / a = H - 3 / 5 * (g * H / a) := by
    dsimp [a, b]
    field_simp
    ring
  change t ≤ W ∧ 269 / 100 ≤ Real.log (d - 1 : ℕ) -
    ((d - 1 : ℕ) : ℝ) * z / (1 - z)
  rw [hid]
  rw [hbg] at hrz
  exact ⟨htW, by dsimp [a] at hrz; linarith⟩

/-- The upper threshold has a finite exponential loss of at most `1/100`.
There is no feasibility assumption: an over-budget threshold has zero tail probability. -/
theorem band_simplex_upper_exponent (g H : ℝ) (d m : ℕ)
    (hd : 1000 ≤ d) (hH : 1 ≤ H) (hg : 0 ≤ g)
    (hsmall : 1000 * H ^ 2 ≤ d) (hmsmall : 1000 * H ^ 2 ≤ m)
    (hgap : 11 / 2 ≤ g * H / (1 + g / 2))
    (hharm : 1 / 2 ≤ H - Real.log (d - 1 : ℕ)) :
    let W := Nat.floor ((1 + g / 2) * d * m / H)
    let t := Nat.ceil ((1 + 13 * g / 20) * m) + 1
    Real.log (d - 1 : ℕ) - ((d - 1 : ℕ) : ℝ) * t /
      ((W : ℝ) + (d - 1 : ℕ)) ≤ -(263 / 200) := by
  let a := 1 + g / 2
  let b := 1 + 13 * g / 20
  let W := Nat.floor (a * d * m / H)
  let t := Nat.ceil (b * m) + 1
  let y := b * H / a
  let s := H / (a * m)
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hap : 0 < a := by linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hb2 : b ≤ 2 * a := by dsimp [a, b]; linarith
  have hHp : 0 < H := by linarith
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hmp : (0 : ℝ) < m := by nlinarith only [hH, hmsmall]
  have hrp : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
  have hr : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyH : y ≤ 2 * H := by
    apply (div_le_iff₀ hap).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb2) hHp.le]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hden : (0 : ℝ) < (W : ℝ) + (d - 1 : ℕ) := by positivity
  have hf := Nat.floor_le (by positivity : 0 ≤ a * (d : ℝ) * m / H)
  have hwidth : (W : ℝ) + (d - 1 : ℕ) ≤ a * d * m / H + d := by
    dsimp [W]
    linarith
  have ht : b * m ≤ (t : ℝ) := by
    have := Nat.le_ceil (b * (m : ℝ))
    dsimp [t]
    push_cast
    linarith
  have hratio : y * (1 - 1 / d) / (1 + s) ≤
      ((d - 1 : ℕ) : ℝ) * t / ((W : ℝ) + (d - 1 : ℕ)) := by
    calc
      _ = ((d - 1 : ℕ) : ℝ) * (b * m) / (a * d * m / H + d) := by
        rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
        dsimp [y, s]
        field_simp
      _ ≤ ((d - 1 : ℕ) : ℝ) * (b * m) / ((W : ℝ) + (d - 1 : ℕ)) :=
        div_le_div_of_nonneg_left (by positivity) hden hwidth
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht hrp.le) hden.le
  have hscalar : y - y / d - y * s ≤ y * (1 - 1 / d) / (1 + s) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + s)).mpr
    rw [show y / d = y * (1 / d) by ring]
    have hi : 0 ≤ 1 / (d : ℝ) := by positivity
    nlinarith only [mul_nonneg hy (mul_nonneg hs hi), mul_nonneg hy (sq_nonneg s)]
  have hlinear : 1000 * H ≤ d := by nlinarith only [hH, hsmall]
  have herr1 : y / d ≤ 2 / 1000 := by
    apply (div_le_iff₀ hdp).mpr
    linarith
  have herr2 : y * s ≤ 2 / 1000 := by
    calc
      _ ≤ (2 * H) * (H / (a * m)) := mul_le_mul_of_nonneg_right hyH hs
      _ ≤ (2 * H) * (H / m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_left hHp.le hmp (by nlinarith)
      _ = 2 * H ^ 2 / m := by ring
      _ ≤ 2 / 1000 := (div_le_iff₀ hmp).mpr (by linarith)
  have hyg : y = H + 3 / 20 * (g * H / a) := by
    dsimp [y, a, b]
    field_simp
    ring
  change Real.log (d - 1 : ℕ) - ((d - 1 : ℕ) : ℝ) * t /
    ((W : ℝ) + (d - 1 : ℕ)) ≤ -(263 / 200)
  have htotal := hscalar.trans hratio
  dsimp [a] at hyg
  linarith only [htotal, herr1, herr2, hyg, hgap, hharm]

end ReedSolomon.HiddenDerivative
