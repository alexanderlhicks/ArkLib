/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Specification
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Contracts for all-rate Reed-Solomon list decoding up to capacity

This module freezes proposition-valued targets for the all-rate strengthening of hidden-derivative
list decoding. For each positive capacity gap `delta`, all global parameters are chosen before the
block length, dimension, prime field, evaluation set, and received word. In particular, the
derivative order depends on `delta` alone and not on the code rate.

The primary finite threshold is

`messageDim + Nat.ceil (delta * blockLength)`.

The contracts expose both the exact polynomial list at that threshold and ArkLib's canonical
`Code.Lambda` value at relative radius `1 - messageDim / blockLength - delta`. When the threshold
exceeds the block length, the exact list is required to be empty explicitly.

No declaration in this file asserts that these targets have been proved. They are definitions of
the propositions to be discharged by later modules.

## References

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164.
* [Dao, Kominers, Thaler, and Zheng, *Reed-Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], manuscript.
-/

namespace ReedSolomon
namespace AllRateListDecoding

open ListDecoding

noncomputable section

/-- The absolute agreement threshold used by the all-rate theorem. -/
def agreementThreshold (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  messageDim + Nat.ceil (delta * (blockLength : ℝ))

/-- The corresponding real-valued radius in ArkLib's `Code.Lambda` convention. -/
def capacityRadius (delta : ℝ) (blockLength messageDim : ℕ) : ℝ :=
  1 - (messageDim : ℝ) / blockLength - delta

/-- The set of all degree-bounded polynomials meeting the absolute agreement threshold. -/
def agreeingPolynomials {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim minAgreement : ℕ) (received : index → F) :
    Set (MessagePolynomial F messageDim) :=
  {p | minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received}

/-- No polynomial can meet an agreement threshold strictly larger than the block length. -/
theorem agreeingPolynomials_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement : ℕ} (hThreshold : Fintype.card index < minAgreement)
    (received : index → F) :
    agreeingPolynomials domain messageDim minAgreement received = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  change minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received at hp
  exact (Nat.not_le_of_lt hThreshold)
    (hp.trans (Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p) (v := received)))

/-- A list bound with a gap-dependent prefactor and exponent overhead.

The exponent is written as `2 * derivOrder + exponentOverhead`, so an initial
`q ^ (4 * derivOrder + 6)` bound is represented by choosing
`exponentOverhead = 2 * derivOrder + 6`. -/
def qualitativeListBound
    (fieldSize derivOrder listFactor exponentOverhead : ℕ) : ℕ :=
  listFactor * fieldSize ^ (2 * derivOrder + exponentOverhead)

/-- A fixed-instance certificate synchronizing exact polynomial decoding and `Code.Lambda`.

The last field deliberately records the `agreementThreshold > blockLength` case, even though it
also follows from exactness. Keeping the branch in the capstone interface prevents it from being
lost when the threshold and radius formulations are connected through floor and ceiling lemmas. -/
structure CapacityGapCertificate (delta : ℝ) {blockLength fieldSize : ℕ}
    (domain : Fin blockLength ↪ ZMod fieldSize) (messageDim listBound : ℕ) where
  /-- An exact decoder for the integral agreement threshold. -/
  decoderCertificate : DecoderCertificate domain messageDim
    (agreementThreshold delta blockLength messageDim) listBound
  /-- The canonical maximized point-list bound at the capacity-gap radius. -/
  lambda_le :
    Code.Lambda (ReedSolomon.code domain messageDim : Set (Fin blockLength → ZMod fieldSize))
      (capacityRadius delta blockLength messageDim) ≤ (listBound : ℕ∞)
  /-- The requested list is empty when the integral threshold exceeds the block length. -/
  empty_of_threshold_exceeds :
    blockLength < agreementThreshold delta blockLength messageDim →
      ∀ received, decoderCertificate.decoder received = ∅

/-- Package an exact decoder and a `Lambda` bound into a capacity-gap certificate. The explicit
oversized-threshold field is discharged from exactness rather than imposed as new evidence. -/
def CapacityGapCertificate.ofDecoderCertificate (delta : ℝ)
    {blockLength fieldSize : ℕ} {domain : Fin blockLength ↪ ZMod fieldSize}
    {messageDim listBound : ℕ}
    (decoderCertificate : DecoderCertificate domain messageDim
      (agreementThreshold delta blockLength messageDim) listBound)
    (lambda_le :
      Code.Lambda (ReedSolomon.code domain messageDim : Set (Fin blockLength → ZMod fieldSize))
        (capacityRadius delta blockLength messageDim) ≤ (listBound : ℕ∞)) :
    CapacityGapCertificate delta domain messageDim listBound where
  decoderCertificate := decoderCertificate
  lambda_le := lambda_le
  empty_of_threshold_exceeds hThreshold received :=
    decoderCertificate.decoder_eq_empty_of_card_lt (by simpa using hThreshold) received

/-- The pointwise combinatorial content for one received word. -/
def PointwiseListBound {blockLength fieldSize : ℕ}
    (delta : ℝ) (domain : Fin blockLength ↪ ZMod fieldSize)
    (messageDim listBound : ℕ) (received : Fin blockLength → ZMod fieldSize) : Prop :=
  (agreeingPolynomials domain messageDim
      (agreementThreshold delta blockLength messageDim) received).encard ≤
        (listBound : ℕ∞) ∧
    (blockLength < agreementThreshold delta blockLength messageDim →
      agreeingPolynomials domain messageDim
        (agreementThreshold delta blockLength messageDim) received = ∅)

/-- A capacity-gap certificate supplies the pointwise polynomial-list bound at every received
word. This checks that the `Finset` decoder and set-valued combinatorial views cannot drift. -/
theorem CapacityGapCertificate.pointwiseListBound {delta : ℝ}
    {blockLength fieldSize : ℕ} {domain : Fin blockLength ↪ ZMod fieldSize}
    {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (received : Fin blockLength → ZMod fieldSize) :
    PointwiseListBound delta domain messageDim listBound received := by
  constructor
  · have hSet :
        agreeingPolynomials domain messageDim
            (agreementThreshold delta blockLength messageDim) received =
          (certificate.decoderCertificate.decoder received :
            Set (MessagePolynomial (ZMod fieldSize) messageDim)) := by
      ext p
      change
        agreementThreshold delta blockLength messageDim ≤
            Code.agree (ReedSolomon.evalOnPoints domain p) received ↔
          p ∈ certificate.decoderCertificate.decoder received
      exact (certificate.decoderCertificate.isExact received p).symm
    rw [hSet, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast certificate.decoderCertificate.card_le received
  · intro hThreshold
    exact agreeingPolynomials_eq_empty_of_card_lt (by simpa using hThreshold) received

/-- **Qualitative all-rate combinatorial target.**

For every fixed positive gap, the derivative order, block-length threshold, list prefactor, and
exponent overhead are selected before every code parameter. The conclusion gives both the
canonical `Lambda` bound and the exact pointwise polynomial-list bound. -/
def QualitativeCombinatorialStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ derivOrder blockLengthThreshold listFactor exponentOverhead : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ (domain : Fin blockLength ↪ ZMod fieldSize),
          let listBound := qualitativeListBound fieldSize derivOrder listFactor exponentOverhead
          Code.Lambda
              (ReedSolomon.code domain messageDim : Set (Fin blockLength → ZMod fieldSize))
              (capacityRadius delta blockLength messageDim) ≤ (listBound : ℕ∞) ∧
            ∀ received : Fin blockLength → ZMod fieldSize,
              PointwiseListBound delta domain messageDim listBound received

/-- **Qualitative all-rate exact-decoder target.**

This strengthens the combinatorial target with one exact decoder for every evaluation set. Its
specification quantifies over all received words internally. -/
def QualitativeExactDecoderStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ derivOrder blockLengthThreshold listFactor exponentOverhead : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          Nonempty <| CapacityGapCertificate delta domain messageDim
            (qualitativeListBound fieldSize derivOrder listFactor exponentOverhead)

/-- **Combined qualitative capstone.**

This is the phase-one target: all rates, arbitrary distinct evaluation points, prime fields of
size at least the block length, and a derivative order depending only on the fixed capacity gap.
The constants may be weaker than the manuscript's optimized constants. -/
def QualitativeAllRateStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ derivOrder blockLengthThreshold listFactor exponentOverhead : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ (domain : Fin blockLength ↪ ZMod fieldSize),
          let listBound := qualitativeListBound fieldSize derivOrder listFactor exponentOverhead
          Nonempty (CapacityGapCertificate delta domain messageDim listBound) ∧
            ∀ received : Fin blockLength → ZMod fieldSize,
              PointwiseListBound delta domain messageDim listBound received

/-- The derivative order in the strong prime-field target.

The order-zero branch covers every gap at least `1 / 4`. Below that boundary, the constant
`169 / 25` is the exact rational representation of `6.76`. -/
def strongDerivativeOrder (delta : ℝ) : ℕ :=
  if (1 / 4 : ℝ) ≤ delta then 0
  else Nat.ceil (Real.exp (((169 : ℝ) / 25) / delta))

@[simp]
theorem strongDerivativeOrder_eq_zero {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta) :
    strongDerivativeOrder delta = 0 := by
  rw [strongDerivativeOrder, if_pos hdelta]

theorem strongDerivativeOrder_eq_ceil {delta : ℝ} (hdelta : delta < (1 / 4 : ℝ)) :
    strongDerivativeOrder delta = Nat.ceil (Real.exp (((169 : ℝ) / 25) / delta)) := by
  rw [strongDerivativeOrder, if_neg (not_le_of_gt hdelta)]

/-- The harmonic number `H_r = sum_{i=1}^r 1/i` used by the asymmetric-band parameters. -/
def harmonicNumber (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range r, (1 : ℝ) / (i + 1)

/-- The optimized asymmetric-band multiplicity `ceil(100 d^2 H_{d-1})`. This parameter package
is used only below gap `1 / 4`; the order-zero branch instead uses an instance-dependent
multiplicity and is deliberately specified separately. -/
def strongBandMultiplicity (delta : ℝ) : ℕ :=
  let derivOrder := strongDerivativeOrder delta
  Nat.ceil (100 * (derivOrder : ℝ) ^ 2 * harmonicNumber (derivOrder - 1))

/-- The ambient dimension in the optimized asymmetric-band certificate. -/
def strongBandAmbientDimension (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  max messageDim ⌊(delta * (blockLength : ℝ)) / 2⌋₊

/-- The larger-field condition under which the asymmetric-band target improves its root exponent
from `2d` to `d`. The truncated natural subtraction represents
`max {0, m * A - K + d}` from the manuscript. -/
def LargeFieldCondition (delta : ℝ)
    (blockLength messageDim fieldSize derivOrder multiplicity : ℕ) :
    Prop :=
  2 * (multiplicity * agreementThreshold delta blockLength messageDim + derivOrder -
    strongBandAmbientDimension delta blockLength messageDim) ≤ fieldSize

/-- **Order-zero target for gaps at least one quarter.**

For gaps at least `1 / 2`, the target list has size at most one. Between `1 / 4` and `1 / 2`,
the target is the manuscript's strict `< 4q` bound. The statement does not require a multiplicity
depending only on the gap: the order-zero interpolation proof uses multiplicity `messageDim - 1`,
with `messageDim = 1` handled directly. -/
def OrderZeroQuarterStatement : Prop :=
  ∀ delta : ℝ, (1 / 4 : ℝ) ≤ delta → delta < 1 →
    ∃ blockLengthThreshold : ℕ,
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          let listBound := if (1 / 2 : ℝ) ≤ delta then 1 else 4 * fieldSize
          Nonempty (CapacityGapCertificate delta domain messageDim listBound) ∧
            (delta < (1 / 2 : ℝ) →
              ∀ received : Fin blockLength → ZMod fieldSize,
                (agreeingPolynomials domain messageDim
                  (agreementThreshold delta blockLength messageDim) received).encard <
                    ((4 * fieldSize : ℕ) : ℕ∞))

/-- **Strong asymmetric-band target below gap one quarter.**

The derivative order and multiplicity are the explicit optimized values from the manuscript.
The block threshold is `8m`. The list bound is `B(delta) * q^(2d)` over every prime field with
`q ≥ n`, improving to `B(delta) * q^d` under `LargeFieldCondition`. -/
def StrongAsymmetricBandStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < (1 / 4 : ℝ) →
    let derivOrder := strongDerivativeOrder delta
    let multiplicity := strongBandMultiplicity delta
    0 < multiplicity ∧
    ∃ listFactor : ℕ, 0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        8 * multiplicity ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          Nonempty (CapacityGapCertificate delta domain messageDim
            (listFactor * fieldSize ^ (2 * derivOrder))) ∧
          (LargeFieldCondition delta blockLength messageDim fieldSize derivOrder multiplicity →
            Nonempty (CapacityGapCertificate delta domain messageDim
              (listFactor * fieldSize ^ derivOrder)))

/-- **Strong quantitative all-rate target.**

The split is load-bearing: derivative order zero above gap `1 / 4` does not imply a constant list
bound in the interval `[1 / 4, 1 / 2)`, and the order-zero multiplicity is not gap-only. -/
def StrongQuantitativeAllRateStatement : Prop :=
  OrderZeroQuarterStatement ∧ StrongAsymmetricBandStatement

end
end AllRateListDecoding
end ReedSolomon
