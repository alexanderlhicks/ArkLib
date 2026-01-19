/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution


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

variable {F : Type} [Field F]

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

theorem irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0) (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  classical
  let f : K[X] →+* K[X] := Polynomial.compRingHom (Polynomial.C a * Polynomial.X)
  let g : K[X] →+* K[X] := Polynomial.compRingHom (Polynomial.C a⁻¹ * Polynomial.X)
  have hCa : (Polynomial.C a⁻¹ * Polynomial.C a : K[X]) = 1 := by
    simpa [Polynomial.C_mul] using (congrArg Polynomial.C (inv_mul_cancel₀ ha))
  have hCb : (Polynomial.C a * Polynomial.C a⁻¹ : K[X]) = 1 := by
    simpa [Polynomial.C_mul] using (congrArg Polynomial.C (mul_inv_cancel₀ ha))
  have hlin₁ : (Polynomial.C a⁻¹ * (Polynomial.C a * Polynomial.X) : K[X]) = Polynomial.X := by
    grind only
  have hlin₂ : (Polynomial.C a * (Polynomial.C a⁻¹ * Polynomial.X) : K[X]) = Polynomial.X := by
    grind only
  have hcomp₁ :
      ((Polynomial.C a⁻¹ * Polynomial.X).comp (Polynomial.C a * Polynomial.X) : K[X]) =
        Polynomial.X := by simp_all only [ne_eq, mul_comp, C_comp, X_comp]
  have hcomp₂ :
      ((Polynomial.C a * Polynomial.X).comp (Polynomial.C a⁻¹ * Polynomial.X) : K[X]) =
        Polynomial.X := by simp_all only [ne_eq, mul_comp, C_comp, X_comp]
  have hf : f.comp g = RingHom.id K[X] := by
    refine RingHom.ext ?_
    intro q
    simp [f, g, Polynomial.comp_assoc, hcomp₁]
  have hg : g.comp f = RingHom.id K[X] := by
    refine RingHom.ext ?_
    intro q
    simp [f, g, Polynomial.comp_assoc, hcomp₂]
  let e : K[X] ≃+* K[X] := RingEquiv.ofRingHom f g hf hg
  simpa [e, f, Polynomial.coe_compRingHom_apply] using
    (MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p))

theorem irreducible_map_univPolyHom_of_irreducible {F : Type} [Field F]
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0) :
    Irreducible H → Irreducible (H.map (ToRatFunc.univPolyHom (F := F))) := by
  intro hH
  classical
  have hprim : H.IsPrimitive := by exact Irreducible.isPrimitive hH hdeg
  have hmap : Irreducible (H.map (algebraMap (Polynomial F) (RatFunc F))) := by
    exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map hprim).mp hH
  exact hmap

theorem irreducibleHTildeOfIrreducible {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hdeg : H.natDegree ≠ 0) :
    (Irreducible H → Irreducible (H_tilde H)) := by
  intro hH
  classical
  -- set up the constants appearing in `H_tilde`
  let d : ℕ := H.natDegree
  let lc : Polynomial F := H.coeff d
  let a : RatFunc F := ToRatFunc.univPolyHom (F := F) lc
  let W : Polynomial (RatFunc F) := Polynomial.C a

  -- `lc` is nonzero (it is the leading coefficient)
  have hH0 : H ≠ 0 := by exact Ne.symm (ne_of_apply_ne natDegree fun a ↦ hdeg (id (Eq.symm a)))
  have hlc0 : lc ≠ 0 := by
    simp_all only [ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true, lc, d]

  -- hence its image in `RatFunc F` is nonzero
  have ha0 : a ≠ 0 := by
    have hinj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
      simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
    intro ha
    apply hlc0
    apply hinj
    have hmap0 : ToRatFunc.univPolyHom (F := F) lc = 0 := by exact ha
    calc
      ToRatFunc.univPolyHom (F := F) lc = 0 := by exact ha
      _ = ToRatFunc.univPolyHom (F := F) 0 := by simp

  -- irreducibility over `RatFunc F`
  have hHmap : Irreducible (H.map (ToRatFunc.univPolyHom (F := F))) := by
    exact irreducible_map_univPolyHom_of_irreducible hdeg hH

  -- linear change of variables: irreducible `p` implies irreducible `p.comp (C a⁻¹ * X)`
  have ha0' : (a⁻¹ : RatFunc F) ≠ 0 := by exact inv_ne_zero ha0
  have hcomp :
      Irreducible
        ((H.map (ToRatFunc.univPolyHom (F := F))).comp (Polynomial.C (a⁻¹) * Polynomial.X)) := by
        exact (irreducible_comp_C_mul_X_iff a⁻¹ ha0' (Polynomial.map univPolyHom H)).mpr hHmap

  -- compute `X / W = C a⁻¹ * X`
  have hS : (Polynomial.X / W) = Polynomial.C (a⁻¹) * Polynomial.X := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := by rfl
      _ = Polynomial.X * Polynomial.C (a⁻¹) := by exact div_C
        -- simpa using (Polynomial.div_C (p := (Polynomial.X : Polynomial (RatFunc F))) (a := a))
      _ = Polynomial.C (a⁻¹) * Polynomial.X := by exact X_mul_C a⁻¹

  -- rewrite the evaluation polynomial `H'` as a composition
  have hEval :
      Polynomial.eval₂
          (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (ToRatFunc.univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := ToRatFunc.univPolyHom (F := F))
            (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
            (x := (Polynomial.X / W))).symm

  -- hence the `eval₂`-polynomial appearing in `H_tilde` is irreducible
  have hH' :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
          (Polynomial.X / W) H) := by grind only

  -- the prefactor `W^(d-1)` is a unit
  have hunitW : IsUnit (W ^ (d - 1)) := by
    have haUnit : IsUnit a := by exact Ne.isUnit ha0
    have hWUnit : IsUnit W := by exact isUnit_C.mpr haUnit
    exact (hWUnit.pow (d - 1))

  rcases hunitW with ⟨u, hu⟩
  have hu' : (u : Polynomial (RatFunc F)) = W ^ (d - 1) := by exact hu

  -- unfold `H_tilde` and finish using `irreducible_units_mul`
  -- (multiplying by a unit does not affect irreducibility)
  -- First, rewrite `H_tilde` into a product with left factor `W^(d-1)`.
  have htilde_unfold :
      H_tilde H =
        (W ^ (d - 1)) *
          (Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
            (Polynomial.X / W) H) := by rfl

  -- now apply the unit-multiplication lemma
  have hirr_prod :
      Irreducible
        ((W ^ (d - 1)) *
          (Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
            (Polynomial.X / W) H)) := by
    -- rewrite the left factor as `↑u`
    simpa [hu'] using
      (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)
          (y :=
            Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
              (Polynomial.X / W) H)).2
        hH'
  exact hirr_prod

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : F[X][Y]} (hdeg : H.natDegree ≠ 0) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible hdeg h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {H : F[X][Y]} [inst : Fact (Irreducible H)]
    [hdeg : Fact (H.natDegree ≠ 0)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible (H := H) hdeg.out inst.out)

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := hᵢ d
  Polynomial.X ^ d +
    ∑ i ∈ (List.range d).toFinset,
      Polynomial.X^(d - 1 - i) *
      Polynomial.C (hᵢ (d - 1 - i) * W ^ i)

lemma H_tilde_equiv_H_tilde' (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  sorry


/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

theorem bivPolyHom_HTilde'_eq_HTilde (H : F[X][Y]) :
    (ToRatFunc.bivPolyHom (F := F)) (H_tilde' H) = H_tilde H := by
  simpa [ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom] using
    (H_tilde_equiv_H_tilde' H)

theorem embeddingOf𝒪Into𝕃_ideal_le (H : F[X][Y]) :
    Ideal.span ({H_tilde' H} : Set F[X][Y]) ≤
      (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))).comap
        (ToRatFunc.bivPolyHom (F := F)) := by
  classical
  -- Reduce to showing the generator lies in the comap ideal
  rw [Ideal.span_singleton_le_iff_mem]
  -- Unfold membership in a comap ideal and rewrite using the bridging lemma
  simpa [Ideal.mem_comap, bivPolyHom_HTilde'_eq_HTilde H] using
    (Ideal.subset_span (by
      simp : (H_tilde H) ∈ ({H_tilde H} : Set (Polynomial (RatFunc F)))))

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) :
    𝒪 H →+* 𝕃 H := by
  classical
  refine
    Ideal.quotientMap
      (I := Ideal.span ({H_tilde' H} : Set F[X][Y]))
      (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))))
      (ToRatFunc.bivPolyHom (F := F))
      (embeddingOf𝒪Into𝕃_ideal_le H)

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

/-- `π_z_lift` annihilates `H_tilde'`. -/
theorem pi_z_lift_H_tilde'_eq_zero {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    π_z_lift (H := H) z root (H_tilde' H) = 0 := by
  classical
  simpa [π_z_lift] using root.property

/-- The kernel of `π_z_lift` contains the span of `H_tilde'`. -/
theorem pi_z_lift_span_le_ker {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    Ideal.span {H_tilde' H} ≤ RingHom.ker (π_z_lift (H := H) z root) := by
  classical
  refine
    (Ideal.span_singleton_le_iff_mem (I := RingHom.ker (π_z_lift (H := H) z root))
          (x := H_tilde' H)).2 ?_
  exact (RingHom.mem_ker).2 (pi_z_lift_H_tilde'_eq_zero (H := H) z root)

/-- `π_z_lift` vanishes on the span of `H_tilde'`. -/
theorem pi_z_lift_vanishes_on_span {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    ∀ a, a ∈ Ideal.span {H_tilde' H} → π_z_lift (H := H) z root a = 0 := by
  intro a ha
  have hker : a ∈ RingHom.ker (π_z_lift (H := H) z root) :=
    (pi_z_lift_span_le_ker (H := H) z root) ha
  exact (RingHom.mem_ker (f := π_z_lift (H := H) z root)).1 hker

/-- The rational substitution map `𝒪 H →+* F` obtained by descending `π_z_lift`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    𝒪 H →+* F := by
  classical
  refine Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift (H := H) z root) ?_
  intro a ha
  exact pi_z_lift_vanishes_on_span (H := H) z root a ha

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

variable {F : Type} [Field F]
         {R : F[X][X][Y]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_natDegree_pos : Fact (H.natDegree ≠ 0)]

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
    𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X;
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
  ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  sorry

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] : 𝒪 H :=
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
                [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
                {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H, weight_Λ_over_𝒪 β ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := by
  sorry

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  (β_regular R H (Nat.le_refl _) t).choose

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) / (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H)) ^ (2*t - 1))

/-- The Hensel lift coefficients `α'` with bundled irreducibility witness. -/
def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H))

/-- The power series `γ'` with bundled irreducibility witness. -/
def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩)

end ClaimA2
end
end BCIKS20AppendixA
