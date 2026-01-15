/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree



/-!
  # Definitions and Theorems about Function Fields and Rings of Regular Functions

  We define the notions of Appendix A of [BCIKS20].

  ## References

  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S.,
      *Proximity Gaps for Reed-Solomon Codes*][BCIKS20]

  ## Main Definitions

-/

open Polynomial
open Polynomial.Bivariate
open ToRatFunc
open Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20] and H_tilde in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

/-- The monisized version H_tilde is irreducible if the originial polynomial H is irreducible. -/
lemma irreducibleHTildeOfIrreducible {H : Polynomial (Polynomial F)} :
    (Irreducible H → Irreducible (H_tilde H)) := by
  sorry

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : F[X][Y]} : Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {H : F[X][Y]} [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible inst.out)

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := hᵢ d
  Polynomial.X ^ d +
    ∑ i ∈ (List.range d).toFinset,
      Polynomial.X^(d - 1 - i) *
      Polynomial.C (hᵢ (d - 1 - i) * W ^ i)


/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H := by
  apply Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        bivPolyHom
        sorry

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial.
-/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
  F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) : 𝒪 H →+* F := by
  apply Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root)
  sorry

/-- The canonical representative of an element of `F[X][Y]` inside
the ring of regular elements `𝒪`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (β : 𝒪 H) : F[X][Y] :=
  Polynomial.modByMonic β.out (H_tilde' H)

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20].
-/
def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (f : 𝒪 H) (D : ℕ)
: WithBot ℕ := weight_Λ (canonicalRepOf𝒪 f) H D

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 {H : F[X][Y]} (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  sorry

/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embeddining of the coefficients of a bivarite polynomial into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The embeddining of the scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

noncomputable def polyToPowerSeries𝕃 (H : F[X][Y])
  (P : F[X][Y])
    : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n =>
    liftToFunctionField (P.coeff n)


end

noncomputable section

namespace ClaimA2

variable {F : Type} [CommRing F] [IsDomain F]
         {R : F[X][X][Y]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)] : 𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X;
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)] :
  ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  sorry

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)] : 𝒪 H :=
  (ξ_regular x₀ R H).choose

/-- The bound of the weight `Λ` of the elements `ζ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma weight_ξ_bound (x₀ : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
  weight_Λ_over_𝒪 (ξ x₀ R H) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  sorry

/-- There exist regular elements `β` with a weight bound as given in Claim A.2
of Appendix A.4 of [BCIKS20]. -/
lemma β_regular (R : F[X][X][Y])
                (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
                {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H, weight_Λ_over_𝒪 β ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := by
  sorry

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  (β_regular R H (Nat.le_refl _) t).choose

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)] (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) / (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H)) ^ (2*t - 1))

def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)] : PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H))

def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩)

end ClaimA2
end
end BCIKS20AppendixA


open Polynomial
open Polynomial.Bivariate
open ToRatFunc
open Ideal
open BCIKS20AppendixA
open scoped BigOperators

theorem C_mul_X_div_C {F : Type} [CommRing F] [IsDomain F] {w : RatFunc F} (hw : w ≠ 0) :
  (Polynomial.C w : Polynomial (RatFunc F)) * (Polynomial.X / Polynomial.C w) = Polynomial.X := by
  classical
  -- Rewrite division by a constant polynomial
  rw [Polynomial.div_C]
  -- Rearrange factors and simplify
  calc
    (Polynomial.C w : Polynomial (RatFunc F)) * (Polynomial.X * Polynomial.C (w⁻¹))
        = Polynomial.X * ((Polynomial.C w : Polynomial (RatFunc F)) * Polynomial.C (w⁻¹)) := by
          ac_rfl
    _ = Polynomial.X * Polynomial.C (w * w⁻¹) := by
          simp [Polynomial.C_mul]
    _ = Polynomial.X := by
          simp [hw]


theorem H_tilde'_map_explicit {F : Type} [CommRing F] [IsDomain F] (H : F[X][Y]) :
  (H_tilde' H).map univPolyHom =
    Polynomial.X ^ H.natDegree +
      ∑ i ∈ Finset.range H.natDegree,
        Polynomial.X ^ (H.natDegree - 1 - i) *
          (Polynomial.C (univPolyHom (H.coeff (H.natDegree - 1 - i))) *
            Polynomial.C (univPolyHom H.leadingCoeff) ^ i) := by
  classical
  simp [H_tilde', List.toFinset_range, Polynomial.map_sum]

theorem H_tilde_eq_sum_range {F : Type} [CommRing F] [IsDomain F] (H : F[X][Y]) :
  H_tilde H =
    Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
      ∑ k ∈ Finset.range (H.natDegree + 1),
        Polynomial.C (univPolyHom (H.coeff k)) *
          (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k := by
  classical
  simp [BCIKS20AppendixA.H_tilde, Polynomial.eval₂_eq_sum_range]

theorem univPolyHom_injective {F : Type} [CommRing F] [IsDomain F] :
  Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))


theorem H_tilde_eq_explicit_forward {F : Type} [CommRing F] [IsDomain F] (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
  H_tilde H =
    Polynomial.X ^ H.natDegree +
      ∑ k ∈ Finset.range H.natDegree,
        Polynomial.X ^ k *
          (Polynomial.C (univPolyHom (H.coeff k)) *
            Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k)) := by
  classical
  have hH0 : H ≠ 0 := by
    intro h0
    simpa [h0] using hdeg
  have hlead : H.leadingCoeff ≠ 0 := by
    simpa using (leadingCoeff_ne_zero.2 hH0)
  have hw : univPolyHom H.leadingCoeff ≠ (0 : RatFunc F) := by
    intro hw0
    apply hlead
    apply (univPolyHom_injective (F := F))
    simpa using hw0

  -- expand H_tilde using the range-sum formula
  rw [H_tilde_eq_sum_range (F := F) (H := H)]

  -- split off the top term k = natDegree
  have hsplit :
      (∑ k ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff k)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) =
        (∑ k ∈ Finset.range H.natDegree,
          Polynomial.C (univPolyHom (H.coeff k)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) +
          Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
    -- `Finset.sum_range_succ` rewrites the sum over `range (d+1)`
    simpa using
      (Finset.sum_range_succ
        (fun k =>
          Polynomial.C (univPolyHom (H.coeff k)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k)
        H.natDegree)

  rw [hsplit, mul_add]

  -- top term becomes X^natDegree
  have hcoeff_nat : H.coeff H.natDegree = H.leadingCoeff := by
    simpa using (Polynomial.coeff_natDegree H)

  have htop :
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree) =
        Polynomial.X ^ H.natDegree := by
    -- rewrite `H.coeff H.natDegree`
    rw [hcoeff_nat]
    have hd1 : (H.natDegree - 1) + 1 = H.natDegree :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hdeg)
    calc
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (Polynomial.C (univPolyHom H.leadingCoeff) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree)
          = (Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
              Polynomial.C (univPolyHom H.leadingCoeff)) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
                simp [mul_assoc, mul_left_comm, mul_comm]
      _ = Polynomial.C (univPolyHom H.leadingCoeff) ^ ((H.natDegree - 1) + 1) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
                -- rewrite `a^(d-1) * a` as `a^((d-1)+1)`
                rw [← pow_succ (Polynomial.C (univPolyHom H.leadingCoeff)) (H.natDegree - 1)]
      _ = Polynomial.C (univPolyHom H.leadingCoeff) ^ H.natDegree *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
                simpa [hd1]
      _ =
          (Polynomial.C (univPolyHom H.leadingCoeff) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))) ^ H.natDegree := by
                -- reverse `mul_pow`
                simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
                  (mul_pow
                      (Polynomial.C (univPolyHom H.leadingCoeff))
                      (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))
                      H.natDegree).symm
      _ = Polynomial.X ^ H.natDegree := by
                -- use the dedicated cancellation lemma
                rw [C_mul_X_div_C (F := F) (w := univPolyHom H.leadingCoeff) (hw := hw)]

  -- lower terms: distribute the outer factor into the sum and simplify termwise
  have hlow :
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (∑ k ∈ Finset.range H.natDegree,
              Polynomial.C (univPolyHom (H.coeff k)) *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) =
        ∑ k ∈ Finset.range H.natDegree,
          Polynomial.X ^ k *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k)) := by
    -- push the outer factor inside
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < H.natDegree := Finset.mem_range.mp hk
    have hkle : k ≤ H.natDegree - 1 := Nat.le_pred_of_lt hklt
    have hsplitExp : H.natDegree - 1 = (H.natDegree - 1 - k) + k :=
      (Nat.sub_add_cancel hkle).symm
    have hpowSplit :
        Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ ((H.natDegree - 1 - k) + k) := by
      exact congrArg
        (fun n => Polynomial.C (univPolyHom H.leadingCoeff) ^ n)
        hsplitExp
    calc
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (Polynomial.C (univPolyHom (H.coeff k)) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k)
          =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ ((H.natDegree - 1 - k) + k) *
              (Polynomial.C (univPolyHom (H.coeff k)) *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) := by
                -- rewrite the power using `hpowSplit`
                rw [hpowSplit]
      _ =
          (Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
              Polynomial.C (univPolyHom H.leadingCoeff) ^ k) *
            (Polynomial.C (univPolyHom (H.coeff k)) *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) := by
                -- split the power using `pow_add`
                rw [pow_add]
      _ =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              (Polynomial.C (univPolyHom H.leadingCoeff) ^ k *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k)) := by
                -- reassociate/commute factors
                ac_rfl
      _ =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              (Polynomial.C (univPolyHom H.leadingCoeff) *
                  (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))) ^ k) := by
                -- combine the k-th powers
                rw [(mul_pow
                      (Polynomial.C (univPolyHom H.leadingCoeff))
                      (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))
                      k).symm]
      _ =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
            (Polynomial.C (univPolyHom (H.coeff k)) * Polynomial.X ^ k) := by
                -- simplify `C w * (X / C w)` to `X`
                rw [C_mul_X_div_C (F := F) (w := univPolyHom H.leadingCoeff) (hw := hw)]
      _ =
          Polynomial.X ^ k *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k)) := by
                ac_rfl

  -- finish by rewriting and using commutativity of addition
  rw [hlow, htop]
  simpa [add_comm, add_left_comm, add_assoc]

theorem H_tilde_eq_explicit {F : Type} [CommRing F] [IsDomain F] (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
  H_tilde H =
    Polynomial.X ^ H.natDegree +
      ∑ i ∈ Finset.range H.natDegree,
        Polynomial.X ^ (H.natDegree - 1 - i) *
          (Polynomial.C (univPolyHom (H.coeff (H.natDegree - 1 - i))) *
            Polynomial.C (univPolyHom H.leadingCoeff) ^ i) := by
  classical
  -- Define the summand from the “forward” explicit formula.
  let f : ℕ → Polynomial (RatFunc F) := fun k =>
    Polynomial.X ^ k *
      (Polynomial.C (univPolyHom (H.coeff k)) *
        Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k))
  -- Start from the forward-indexed explicit formula and reflect the index using
  -- `Finset.sum_range_reflect`.
  calc
    H_tilde H =
        Polynomial.X ^ H.natDegree +
          ∑ k ∈ Finset.range H.natDegree, f k := by
          simpa [f] using (H_tilde_eq_explicit_forward (H := H) hdeg)
    _ =
        Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree, f (H.natDegree - 1 - i) := by
          -- reindex the finite sum by reflection
          congr 1
          simpa using (Finset.sum_range_reflect f H.natDegree).symm
    _ =
        Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.X ^ (H.natDegree - 1 - i) *
              (Polynomial.C (univPolyHom (H.coeff (H.natDegree - 1 - i))) *
                Polynomial.C (univPolyHom H.leadingCoeff) ^ i) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi' : i < H.natDegree := Finset.mem_range.mp hi
          have hi_le : i ≤ H.natDegree - 1 := by
            exact Nat.le_pred_of_lt hi'
          -- unfold `f` and simplify the exponent `H.natDegree - 1 - (H.natDegree - 1 - i)`
          simp [f, tsub_tsub_cancel_of_le hi_le]


theorem H_tilde_equiv_H_tilde' {F : Type} [CommRing F] [IsDomain F] (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
  (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  simpa [H_tilde'_map_explicit (H := H), H_tilde_eq_explicit (H := H) hdeg]
