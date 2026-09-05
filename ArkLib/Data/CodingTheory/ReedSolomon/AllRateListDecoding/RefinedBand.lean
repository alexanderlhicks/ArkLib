/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors

Adapts Quang Dao's StrongBand.lean construction to the improved quantitative parameters.
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.AgreementRadius
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.BandConstruction
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.RefinedBandParameters
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.LowOrderRegime

/-!
# Quantitative all-rate list bounds with derivative-order constant `5.5`

For `0 < δ < 1/4`, put `d = ceil(exp((11/2)/δ))`, `H = H_(d-1)`, and
`m = ceil(100 d² H)`. For every `n ≥ 8m`, every `1 ≤ k ≤ n`, every prime `q ≥ n`,
and every injective evaluation domain in `ZMod q`, the capacity-gap list has size at most
`floor(32 (d+1) m² q^(2d) / 7)`. The same parameters give an actual nonzero
hidden-derivative interpolant, not merely a smaller numerical list exponent.

The original larger-field condition gives the separate bound `8 (d+1) m² q^d`.
The existing order-zero list theorems cover the remaining gaps. No evaluation-domain
extension is required, including when `q = n`. Exact decoders here are classical finite-set
witnesses: no executable interpolation procedure or runtime bound is asserted.
-/

namespace ReedSolomon.AllRateListDecoding

noncomputable section

open HiddenDerivative ListDecoding

/-- Numerical band data shared by the improved construction and root-count frontends. -/
private structure RefinedBandInstanceData (n k A d m K : ℕ) where
  W : ℕ
  Cmin : ℕ
  Cmax : ℕ
  L : ℝ
  order_pos : 0 < d
  order_lt : d < K - 1
  message_le : k ≤ K
  ambient_le : K ≤ n
  product_pos : 0 < m * A
  cutoff_agreement : L ≤ (m * A : ℕ)
  cutoff_jet : L ≤ ((K - 1 : ℕ) : ℝ) * (2 * m : ℕ)
  comparison : n * asymmetricBandLocalBudget d m W ⌈L / (K - 1 : ℕ) - Cmin⌉₊ <
    asymmetricBandDimensionCount (K - 1) d m W Cmin Cmax L

/-- The improved prescribed parameters satisfy every premise of the construction bridge. -/
private theorem exists_refined_band_instance_data {δ : ℝ} {n k : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    Nonempty (RefinedBandInstanceData n k (agreementThreshold δ n k)
      (refinedDerivativeOrder δ) (refinedBandMultiplicity δ)
      (strongBandAmbientDimension δ n k)) := by
  let d := refinedDerivativeOrder δ
  let m := refinedBandMultiplicity δ
  let K := strongBandAmbientDimension δ n k
  let D := K - 1
  let g := min 1 (δ / ((D : ℝ) / n))
  let H := harmonicNumber (d - 1)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  have hblock' : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp ((11 / 2) / δ)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp ((11 / 2) / δ)) - 1)) ≤ n := by
    simpa only [refinedBandMultiplicity, refinedDerivativeOrder_eq_ceil hδ'] using hblock
  obtain ⟨_, hD, hdD, _, _⟩ :=
    band_block_size_bounds_of_constant (11 / 2) δ n k (by norm_num) hδ hδ' hk hblock' hA
  have hdD' : d < D := by
    simpa only [d, refinedDerivativeOrder_eq_ceil hδ'] using hdD
  have hm : 0 < m := refinedBandMultiplicity_pos hδ hδ'
  have hn : 0 < n := hk.trans_le hkn
  have hD' : 0 < D := hD
  have hd : 0 < d := by
    dsimp only [d]
    rw [refinedDerivativeOrder_eq_ceil hδ']
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hKn : K ≤ n := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ δ * (n : ℝ) / 2)
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpad : (Nat.floor (δ * (n : ℝ) / 2) : ℝ) ≤ n := by nlinarith
    exact max_le hkn (by exact_mod_cast hpad)
  have hAreal : (k : ℝ) + δ * n ≤ agreementThreshold δ n k :=
    (agreementThreshold_le_iff_real hδ.le _ _ _).mp le_rfl
  have hslack : (D : ℝ) * (1 + g) ≤ agreementThreshold δ n k := by
    have h := strongBandAmbientDegree_slack_le_agreement hδ hk hD' hAreal
    simpa only [g, band_relativeSlack_rate_eq hn hD'] using h
  have hg1 : g ≤ 1 := min_le_left _ _
  have hL : (D : ℝ) * m * (1 + g) ≤ (m * agreementThreshold δ n k : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    push_cast
    nlinarith only [h]
  have hLt : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hg1
      (by positivity : (0 : ℝ) ≤ (D : ℝ) * m)
    push_cast
    nlinarith only [h]
  have hdim := refined_band_budget_lt_dimensionCount δ n k hδ hδ' hk hblock hA
  have hquot : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
    have hDn : (D : ℝ) ≠ 0 := by positivity
    field_simp
  refine ⟨{
    W := W, Cmin := Cmin, Cmax := Cmax, L := (D : ℝ) * m * (1 + g)
    order_pos := hd, order_lt := hdD', message_le := Nat.le_max_left _ _
    ambient_le := hKn, product_pos := Nat.mul_pos hm (hk.trans_le (Nat.le_add_right _ _))
    cutoff_agreement := hL, cutoff_jet := hLt, comparison := ?_
  }⟩
  change n * asymmetricBandLocalBudget d m W
    ⌈(D : ℝ) * m * (1 + g) / D - Cmin⌉₊ < _
  simpa only [hquot] using hdim

/-- An actual hidden-derivative construction at the improved order and multiplicity.
Only feasible agreement thresholds need a nonzero interpolant. -/
theorem refined_hidden_derivative_construction {δ : ℝ} {n k q : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hq : q.Prime) (hnq : n ≤ q) (hA : agreementThreshold δ n k ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    ∃ construction : HiddenDerivativeConstruction (k := k) (A := agreementThreshold δ n k)
        (refinedDerivativeOrder δ) (refinedBandMultiplicity δ) domain received,
      construction.ambientDim = strongBandAmbientDimension δ n k ∧
        ∀ j, jetDegree construction.interpolant j ≤ 2 * refinedBandMultiplicity δ := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨data⟩ := exists_refined_band_instance_data hδ hδ' hblock hk hkn hA
  have hm := refinedBandMultiplicity_pos hδ hδ'
  have hmq : 2 * refinedBandMultiplicity δ < q := by omega
  have hcontact := band_contact_budget_le_eighth hblock hA hnq
  exact exists_band_construction domain received data.message_le data.ambient_le hnq
    data.order_pos data.order_lt data.product_pos hmq (by omega)
    data.cutoff_agreement data.cutoff_jet data.comparison

/-- The improved exact-list bound over every prime field `q ≥ n` and every evaluation set.
The natural division is taken after multiplication by the field power. -/
theorem refined_band_pointwise_div_seven {δ : ℝ} {n k q : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hq : q.Prime) (hnq : n ≤ q)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    (agreeingPolynomials domain k (agreementThreshold δ n k) received).encard ≤
      ((32 * (refinedDerivativeOrder δ + 1) * refinedBandMultiplicity δ ^ 2 *
        q ^ (2 * refinedDerivativeOrder δ)) / 7 : ℕ) := by
  let : Fact q.Prime := ⟨hq⟩
  by_cases hA : agreementThreshold δ n k ≤ n
  · obtain ⟨data⟩ := exists_refined_band_instance_data hδ hδ' hblock hk hkn hA
    have hm := refinedBandMultiplicity_pos hδ hδ'
    have hchar : strongBandAmbientDimension δ n k - 1 < ringChar (ZMod q) := by
      rw [ringChar.eq (ZMod q) q]
      have := data.ambient_le
      have := data.order_lt
      omega
    have hmchar : 2 * refinedBandMultiplicity δ < ringChar (ZMod q) := by
      rw [ringChar.eq (ZMod q) q]
      omega
    have hcontact := band_contact_budget_le_eighth hblock hA hnq
    have hlarge : 8 * (refinedBandMultiplicity δ * agreementThreshold δ n k +
        refinedDerivativeOrder δ - strongBandAmbientDimension δ n k) ≤ q ^ 2 := by
      have := data.order_lt
      omega
    have h := agreeingPolynomials_encard_le_div_seven_of_band_certificate domain received
      data.message_le data.order_pos data.order_lt data.product_pos hchar hmchar
      (by norm_num : 0 < (2 : ℕ)) (by simpa only [Nat.card_zmod] using hlarge)
      data.cutoff_agreement data.cutoff_jet data.comparison
    simpa only [Nat.card_zmod] using h
  · rw [agreeingPolynomials_eq_empty_of_card_lt (by simpa using Nat.lt_of_not_ge hA) received]
    simp

/-- The canonical exact decoder and relative-radius certificate at derivative constant `5.5`.
This includes `Code.Lambda` and the oversized-threshold empty-list guarantee. -/
theorem refined_band_certificate_div_seven {δ : ℝ} {n k q : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hq : q.Prime) (hnq : n ≤ q) (domain : Fin n ↪ ZMod q) :
    Nonempty (CapacityGapCertificate δ domain k
      ((32 * (refinedDerivativeOrder δ + 1) * refinedBandMultiplicity δ ^ 2 *
        q ^ (2 * refinedDerivativeOrder δ)) / 7)) := by
  exact ⟨CapacityGapCertificate.ofPointwiseBound hδ.le (hk.trans_le hkn) domain
    (refined_band_pointwise_div_seven hδ hδ' hblock hk hkn hq hnq domain)⟩

/-- Under the original larger-field condition the improved order also gives exponent `d`.
The weaker half-field budget retains its original prefactor `8`, not `32/7`. -/
theorem refined_band_pointwise_of_large_field {δ : ℝ} {n k q : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hq : q.Prime) (hnq : n ≤ q)
    (hlarge : LargeFieldCondition δ n k q (refinedDerivativeOrder δ) (refinedBandMultiplicity δ))
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    (agreeingPolynomials domain k (agreementThreshold δ n k) received).encard ≤
      (8 * (refinedDerivativeOrder δ + 1) * refinedBandMultiplicity δ ^ 2 *
        q ^ refinedDerivativeOrder δ : ℕ) := by
  let : Fact q.Prime := ⟨hq⟩
  by_cases hA : agreementThreshold δ n k ≤ n
  · obtain ⟨data⟩ := exists_refined_band_instance_data hδ hδ' hblock hk hkn hA
    have hm := refinedBandMultiplicity_pos hδ hδ'
    have hchar : strongBandAmbientDimension δ n k - 1 < ringChar (ZMod q) := by
      rw [ringChar.eq (ZMod q) q]
      have := data.ambient_le
      have := data.order_lt
      omega
    have hmchar : 2 * refinedBandMultiplicity δ < ringChar (ZMod q) := by
      rw [ringChar.eq (ZMod q) q]
      omega
    have h := agreeingPolynomials_encard_le_of_band_certificate domain received
      data.message_le data.order_pos data.order_lt data.product_pos hchar hmchar
      (by norm_num : 0 < (1 : ℕ))
      (by simpa only [Nat.card_zmod, pow_one, LargeFieldCondition] using hlarge)
      data.cutoff_agreement data.cutoff_jet data.comparison
    simpa only [Nat.card_zmod, one_mul] using h
  · rw [agreeingPolynomials_eq_empty_of_card_lt (by simpa using Nat.lt_of_not_ge hA) received]
    simp

/-- The larger-field version in the same canonical capacity-gap interface. -/
theorem refined_band_certificate_of_large_field {δ : ℝ} {n k q : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (hblock : 8 * refinedBandMultiplicity δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hq : q.Prime) (hnq : n ≤ q)
    (hlarge : LargeFieldCondition δ n k q (refinedDerivativeOrder δ) (refinedBandMultiplicity δ))
    (domain : Fin n ↪ ZMod q) :
    Nonempty (CapacityGapCertificate δ domain k
      (8 * (refinedDerivativeOrder δ + 1) * refinedBandMultiplicity δ ^ 2 *
        q ^ refinedDerivativeOrder δ)) := by
  exact ⟨CapacityGapCertificate.ofPointwiseBound hδ.le (hk.trans_le hkn) domain
    (refined_band_pointwise_of_large_field hδ hδ' hblock hk hkn hq hnq hlarge domain)⟩

/-- The improved small-gap quantitative contract, with explicit bounds in both field regimes.
This statement has no runtime or efficient-decoder claim. -/
def RefinedAsymmetricBandStatement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < (1 / 4 : ℝ) →
    let d := refinedDerivativeOrder δ
    let m := refinedBandMultiplicity δ
    0 < m ∧ ∀ n k q : ℕ, 8 * m ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q →
      ∀ domain : Fin n ↪ ZMod q,
        Nonempty (CapacityGapCertificate δ domain k ((32 * (d + 1) * m ^ 2 * q ^ (2 * d)) / 7)) ∧
        (LargeFieldCondition δ n k q d m →
          Nonempty (CapacityGapCertificate δ domain k (8 * (d + 1) * m ^ 2 * q ^ d)))

/-- Both quantitative small-gap branches hold at the improved derivative order. -/
theorem refined_asymmetric_band : RefinedAsymmetricBandStatement := by
  intro δ hδ hδ'
  refine ⟨refinedBandMultiplicity_pos hδ hδ', ?_⟩
  intro n k q hblock hk hkn hq hnq domain
  exact ⟨refined_band_certificate_div_seven hδ hδ' hblock hk hkn hq hnq domain,
    fun hlarge ↦ refined_band_certificate_of_large_field hδ hδ' hblock hk hkn hq hnq hlarge domain⟩

/-- The fully quantified all-rate list theorem: the improved small-gap construction is combined
with the existing order-zero list regime at and above one quarter. -/
theorem refined_quantitative_all_rate :
    OrderZeroQuarterStatement ∧ RefinedAsymmetricBandStatement :=
  ⟨orderZeroQuarterStatement, refined_asymmetric_band⟩

end
end ReedSolomon.AllRateListDecoding
