/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.OuterMeasure.Basic

open NNReal ProximityGap

/-!
  # Definitions and Theorems about Divergence of Sets

  ## Main Definitions and Statements

  - divergence of sets
  - statement of Corollary 1.3 (Concentration bounds) from [BCIKS20].
-/

namespace DivergenceOfSets

open Code ReedSolomonCode ProbabilityTheory

section Defs

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [DecidableEq F]
         {U V : Set (ι → F)} [Nonempty V] [Fintype V]

/-- The set of possible relative Hamming distances between two sets. -/
def possibleDeltas (U V : Set (ι → F)) [Nonempty V] [Fintype V] : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ u ∈ U, δᵣ'(u,V) = d}

/-- The set of possible relative Hamming distances between two sets is well-defined. -/
@[simp]
lemma possibleDeltas_subset_relHammingDistRange :
  possibleDeltas U V ⊆ relHammingDistRange ι :=
  fun x hx_mem_deltas ↦ by
    simp only [possibleDeltas, Set.mem_setOf_eq] at hx_mem_deltas
    rcases hx_mem_deltas with ⟨u, hu_mem, h_dist_eq⟩
    rw [←h_dist_eq]
    unfold relDistFromCode'
    have h_mem : (Finset.univ.image (fun (c : V) => relHammingDist u c)).min'
      (Finset.univ_nonempty.image _) ∈ Finset.univ.image (fun (c : V) => relHammingDist u c) :=
      Finset.min'_mem _ (Finset.univ_nonempty.image _)
    obtain ⟨c, _, h_eq⟩ := Finset.mem_image.mp h_mem
    rw [←h_eq]
    exact relHammingDist_mem_relHammingDistRange

/-- The set of possible relative Hamming distances between two sets is finite. -/
@[simp]
lemma finite_possibleDeltas : (possibleDeltas U V).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDeltas_subset_relHammingDistRange

open Classical in
/-- Definition of divergence of two sets from Section 1.2 in [BCIKS20].

For two sets `U` and `V`, the divergence of `U` from `V` is the maximum of the possible
relative Hamming distances between elements of `U` and the set `V`. -/
noncomputable def divergence (U V : Set (ι → F)) [Nonempty V] [Fintype V] : ℚ≥0 :=
  haveI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
  if h : (possibleDeltas U V).Nonempty
  then (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

end Defs

section Theorems

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Fintype F] [Field F]
         {U V : Set (ι → F)}

end Theorems

end DivergenceOfSets

open Classical
open Affine
open Code
open ProximityGap
open ReedSolomonCode
open ProbabilityTheory
open scoped ProbabilityTheory
open scoped NNReal

theorem affSpanFinset_eq_of_range_eq {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {U : AffineSubspace F (ι → F)} [Nonempty U] [NeZero (Fintype.card U)]
  (uGen : Fin (Fintype.card U) → (ι → F))
  (huGen_range : Set.range uGen = (U : Set (ι → F))) :
  (Affine.AffSpanFinset uGen : Set (ι → F)) = (U : Set (ι → F)) := by
  classical
  have hfin : (Affine.AffSpanFinset uGen : Set (ι → F)) = Affine.AffSpanSet uGen := by
    simpa [Affine.AffSpanFinset] using
      (Set.Finite.coe_toFinset (s := Affine.AffSpanSet uGen)
        (Affine.AffSpanSet.instFinite (u := uGen)))
  rw [hfin]
  unfold Affine.AffSpanSet
  have himage : ((Finset.univ.image uGen : Finset (ι → F)) : Set (ι → F)) = Set.range uGen := by
    ext x
    simp [Set.range]
  rw [himage]
  rw [huGen_range]
  change ((affineSpan F (U : Set (ι → F)) : AffineSubspace F (ι → F)) : Set (ι → F)) = (U : Set (ι → F))
  exact
    congrArg (fun S : AffineSubspace F (ι → F) => (S : Set (ι → F)))
      (AffineSubspace.affineSpan_coe (s := U))

theorem affineSubspace_exists_enum {ι : Type} [Fintype ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (U : AffineSubspace F (ι → F)) [Nonempty U] :
  ∃ uGen : Fin (Fintype.card U) → (ι → F), Set.range uGen = (U : Set (ι → F)) := by
  classical
  let e : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  refine ⟨fun i => (e i : (ι → F)), ?_⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    -- show that the chosen index maps to x
    simpa [e] using congrArg (fun (y : U) => (y : (ι → F))) (e.apply_symm_apply ⟨x, hx⟩)


theorem divergence_exists_witness {ι : Type} [Fintype ι] [Nonempty ι]
  {F : Type} [Fintype F] [DecidableEq F]
  (U V : Set (ι → F)) [Nonempty U] [Nonempty V] [Fintype V] :
  ∃ u ∈ U, δᵣ'(u, V) = DivergenceOfSets.divergence U V := by
  classical
  -- pick an element of `U` to show `possibleDeltas U V` is nonempty
  let u0 : U := Classical.choice (inferInstance : Nonempty U)
  have hD : (DivergenceOfSets.possibleDeltas U V).Nonempty := by
    refine ⟨δᵣ'(u0, V), ?_⟩
    refine ⟨u0, u0.property, rfl⟩
  -- provide a fintype instance for `possibleDeltas U V`
  letI : Fintype (DivergenceOfSets.possibleDeltas U V) :=
    @Fintype.ofFinite _ (DivergenceOfSets.finite_possibleDeltas (U := U) (V := V))
  have hmem :
      DivergenceOfSets.divergence U V ∈ DivergenceOfSets.possibleDeltas U V := by
    -- unfold `divergence`; since `possibleDeltas U V` is nonempty, it is a `max'`
    simp [DivergenceOfSets.divergence, hD]
    -- transfer membership from `toFinset` back to the set
    refine (Set.mem_toFinset).1 ?_
    -- the maximum of a nonempty finset is a member
    exact
      Finset.max'_mem (s := (DivergenceOfSets.possibleDeltas U V).toFinset)
        (Set.toFinset_nonempty.2 hD)
  -- unpack membership in `possibleDeltas` to obtain the witness
  simpa [DivergenceOfSets.possibleDeltas] using hmem

theorem errorBound_mono_on_johnson_interval {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {δ₁ δ₂ : NNReal}
  (hδ : δ₁ ≤ δ₂)
  (hδ₁ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : NNReal)) / 2 < δ₁)
  (hδ₂ : δ₂ < 1 - ReedSolomonCode.sqrtRate deg domain) :
  ProximityGap.errorBound δ₁ deg domain ≤ ProximityGap.errorBound δ₂ deg domain := by
  classical
  -- The lower bound on `δ₁` together with `δ₁ ≤ δ₂` gives the Johnson-regime lower bound for `δ₂`.
  have hδ₂' : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : NNReal)) / 2 < δ₂ :=
    lt_of_lt_of_le hδ₁ hδ
  -- And `δ₁ ≤ δ₂` transfers the Johnson-regime upper bound from `δ₂` to `δ₁`.
  have hδ₁ub : δ₁ < 1 - ReedSolomonCode.sqrtRate deg domain := lt_of_le_of_lt hδ hδ₂
  -- Force both `errorBound` values into the Johnson branch.
  have hnle₁ : ¬δ₁ ≤ (1 - (LinearCode.rate (ReedSolomon.code domain deg) : NNReal)) / 2 :=
    not_le_of_gt hδ₁
  have hnle₂ : ¬δ₂ ≤ (1 - (LinearCode.rate (ReedSolomon.code domain deg) : NNReal)) / 2 :=
    not_le_of_gt hδ₂'
  simp [ProximityGap.errorBound, hnle₁, hnle₂, hδ₁, hδ₂', hδ₁ub, hδ₂]
  -- The remaining inequality is monotone in the denominator; `gcongr` reduces it to
  -- strict positivity of the denominator.
  gcongr

  -- Show the denominator is strictly positive.
  have hcardF_pos : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)

  -- First term in the `min` is positive since `δ₂ < 1 - sqrtRate`.
  have hδ₂_lt_sqrt :
      δ₂ < 1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : NNReal) := by
    simpa [ReedSolomonCode.sqrtRate] using hδ₂
  have hpos₁_nnreal :
      0 < (1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : NNReal) - δ₂ : NNReal) :=
    tsub_pos_of_lt hδ₂_lt_sqrt
  have hpos₁ :
      0 < (↑(1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : NNReal) - δ₂) : ℝ) := by
    exact_mod_cast hpos₁_nnreal

  -- Second term in the `min` is positive since the Reed–Solomon code has positive rate.
  have h_ex : ∃ x : (ReedSolomon.code domain deg), x ≠ 0 := by
    refine ⟨⟨ReedSolomonCode.constantCode (x := (1 : F)) ι, ?_⟩, ?_⟩
    · simpa using
        (ReedSolomonCode.constantCode_mem_code (α := domain) (n := deg) (x := (1 : F)) (ι := ι))
    · intro hx
      have : (ReedSolomonCode.constantCode (x := (1 : F)) ι) = 0 := by
        simpa using congrArg Subtype.val hx
      have : (1 : F) = 0 :=
        (ReedSolomonCode.constantCode_eq_ofNat_zero_iff (ι := ι) (x := (1 : F))).1 this
      exact one_ne_zero this
  have hfinrank_pos : 0 < Module.finrank F (ReedSolomon.code domain deg) := by
    exact
      (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := ReedSolomon.code domain deg)).2 h_ex
  have hrate_pos : 0 < LinearCode.rate (ReedSolomon.code domain deg) := by
    -- `rate = dim / length`, with `dim > 0` (since the code is nontrivial) and `length > 0`.
    dsimp [LinearCode.rate, LinearCode.dim, LinearCode.length]
    have hnum : 0 < (Module.finrank F (ReedSolomon.code domain deg) : ℚ≥0) := by
      exact_mod_cast hfinrank_pos
    have hden : 0 < (Fintype.card ι : ℚ≥0) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    exact div_pos hnum hden
  have hrate_pos_real : 0 < (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ) := by
    exact_mod_cast hrate_pos
  have hpos₂ : 0 < Real.sqrt (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ) / 20 := by
    have hsqrt_pos : 0 < Real.sqrt (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ) := by
      exact Real.sqrt_pos.2 hrate_pos_real
    have h20 : (0 : ℝ) < 20 := by norm_num
    exact div_pos hsqrt_pos h20

  have hmin_pos :
      0 <
        min (↑(1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : NNReal) - δ₂))
          (Real.sqrt (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ) / 20) :=
    lt_min hpos₁ hpos₂

  have hbase_pos :
      0 <
        (2 : ℝ) *
          min (↑(1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : NNReal) - δ₂))
            (Real.sqrt (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ) / 20) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h2 hmin_pos

  have hpow_pos :
      0 <
        ((2 : ℝ) *
              min (↑(1 - NNReal.sqrt (LinearCode.rate (ReedSolomon.code domain deg) : NNReal) - δ₂))
                (Real.sqrt (↑(LinearCode.rate (ReedSolomon.code domain deg)) : ℝ) / 20)) ^
            7 :=
    pow_pos hbase_pos 7

  -- Finish. `simp` normalizes the coercions in the goal.
  simpa using (mul_pos hpow_pos hcardF_pos)

theorem pr_uniformOfFintype_eq_one_iff_forall {α : Type} [Fintype α] [Nonempty α]
  (P : α → Prop) :
  (Pr_{let a ← $ᵖ α}[P a] = (1 : ENNReal)) ↔ (∀ a, P a) := by
  classical
  -- reduce the `Pr` notation to a statement about `PMF.map`
  simp
  -- `simp` leaves us with the `PMF` level statement
  let p : PMF α := $ᵖ α
  let q : PMF Prop := p.map P
  change q True = 1 ↔ ∀ a, P a
  -- rewrite `q True = 1` as a support condition
  rw [PMF.apply_eq_one_iff q True]
  constructor
  · intro hs a
    by_contra hPa
    have ha : a ∈ p.support := by
      -- uniform distribution has full support
      simpa [p, PMF.support_uniformOfFintype] using (show a ∈ (⊤ : Set α) from trivial)
    have hFalse : False ∈ q.support := by
      -- `a` witnesses that `False` is in the support of the pushforward
      refine (PMF.mem_support_map_iff (p := p) (f := P) (b := False)).2 ?_
      refine ⟨a, ha, ?_⟩
      -- turn `¬ P a` into `P a = False`
      apply propext
      constructor
      · intro h
        exact (hPa h).elim
      · intro h
        exact False.elim h
    have : False ∈ ({True} : Set Prop) := by
      simpa [hs] using hFalse
    simpa using this
  · intro hall
    apply le_antisymm
    · intro b hb
      rcases (PMF.mem_support_map_iff (p := p) (f := P) (b := b)).1 hb with ⟨a, ha, hPa⟩
      have hPaTrue : P a = True := by
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          exact hall a
      have : b = True := by
        -- from `P a = b` and `P a = True` we get `b = True`
        simpa [hPaTrue] using hPa.symm
      simpa [this]
    · intro b hb
      have hb' : b = True := by simpa using hb
      subst hb'
      -- show `True` is in the support of `q`
      rcases (inferInstance : Nonempty α) with ⟨a0⟩
      have ha0 : a0 ∈ p.support := by
        simpa [p, PMF.support_uniformOfFintype] using (show a0 ∈ (⊤ : Set α) from trivial)
      refine (PMF.mem_support_map_iff (p := p) (f := P) (b := True)).2 ?_
      refine ⟨a0, ha0, ?_⟩
      apply propext
      constructor
      · intro _
        trivial
      · intro _
        exact hall a0

theorem pr_uniformOfFintype_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
  (e : α ≃ β) (Q : β → Prop) :
  Pr_{let a ← $ᵖ α}[Q (e a)] = Pr_{let b ← $ᵖ β}[Q b] := by
  classical
  -- reduce to a statement about `tsum`
  simp [PMF.monad_map_eq_map]
  -- reindex the left `tsum` along the equivalence `e`
  have htsum : (∑' a : α, if Q (e a) then (Fintype.card α : ENNReal)⁻¹ else 0) =
      ∑' b : β, if Q b then (Fintype.card α : ENNReal)⁻¹ else 0 := by
    simpa using (e.tsum_eq (fun b : β => if Q b then (Fintype.card α : ENNReal)⁻¹ else 0))
  -- match the constants using `Fintype.card_congr`
  have hcard : (Fintype.card α : ENNReal)⁻¹ = (Fintype.card β : ENNReal)⁻¹ := by
    simpa [Fintype.card_congr e]
  -- finish
  rw [htsum]
  simp [hcard]

theorem pr_uniformOfFintype_mono_of_imp {α : Type} [Fintype α] [Nonempty α]
  {P Q : α → Prop}
  (hPQ : ∀ a, P a → Q a) :
  Pr_{let a ← $ᵖ α}[P a] ≤ Pr_{let a ← $ᵖ α}[Q a] := by
  classical
  -- unfold `Pr_{ ... }[...]` into a statement about `PMF`.
  simp [ProbabilityTheory.prStx]
  -- Now rewrite both sides as outer measures of the corresponding events.
  set p : PMF α := $ᵖ α
  have hP : (P <$> p) True = p.toOuterMeasure {a | P a} := by
    calc
      (P <$> p) True = (p.map P) True := by
        simp [PMF.monad_map_eq_map]
      _ = (p.map P).toOuterMeasure ({True} : Set Prop) := by
        simpa using (PMF.toOuterMeasure_apply_singleton (p := p.map P) True).symm
      _ = p.toOuterMeasure (P ⁻¹' ({True} : Set Prop)) := by
        simpa using (PMF.toOuterMeasure_map_apply (p := p) (f := P) (s := ({True} : Set Prop)))
      _ = p.toOuterMeasure {a | P a} := by
        simpa [Set.preimage_singleton_true]
  have hQ : (Q <$> p) True = p.toOuterMeasure {a | Q a} := by
    calc
      (Q <$> p) True = (p.map Q) True := by
        simp [PMF.monad_map_eq_map]
      _ = (p.map Q).toOuterMeasure ({True} : Set Prop) := by
        simpa using (PMF.toOuterMeasure_apply_singleton (p := p.map Q) True).symm
      _ = p.toOuterMeasure (Q ⁻¹' ({True} : Set Prop)) := by
        simpa using (PMF.toOuterMeasure_map_apply (p := p) (f := Q) (s := ({True} : Set Prop)))
      _ = p.toOuterMeasure {a | Q a} := by
        simpa [Set.preimage_singleton_true]
  have hsub : {a | P a} ⊆ {a | Q a} := by
    intro a ha
    exact hPQ a ha
  have hmono : p.toOuterMeasure {a | P a} ≤ p.toOuterMeasure {a | Q a} :=
    MeasureTheory.measure_mono hsub
  simpa [hP, hQ] using hmono

theorem proximity_gap_bound_affineSubspace {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  {δ : NNReal}
  (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  (hδ_lt : δ < (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal)) :
  Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (ReedSolomonCode.RScodeSet domain deg) ≤ δ]
    ≤ ProximityGap.errorBound δ deg domain := by
  classical
  -- Use classical decidable equality on the index type to avoid definitional-equality issues.
  letI : DecidableEq ι := Classical.decEq ι

  -- abbrev for the RS code as a set
  let RS : Set (ι → F) := ReedSolomonCode.RScodeSet domain deg

  -- nonzero cardinality of U (needed for AffSpanFinset)
  haveI : NeZero (Fintype.card U) :=
    ⟨by
      simpa using (Fintype.card_ne_zero (α := U))⟩

  -- enumerate U
  obtain ⟨uGen, huGen_range⟩ :=
    affineSubspace_exists_enum (ι := ι) (F := F) (U := U)

  -- singleton collection for proximity gap
  let C : Fin 1 → (Fin (Fintype.card U) → (ι → F)) := fun _ => uGen
  let S : Finset (ι → F) := Affine.AffSpanFinset uGen

  have hS_mem : S ∈ Affine.AffSpanFinsetCollection C := by
    refine ⟨0, ?_⟩
    simp [C, S]

  -- identify the span finset with U
  have hSU : (S : Set (ι → F)) = (U : Set (ι → F)) :=
    affSpanFinset_eq_of_range_eq (ι := ι) (F := F) (U := U) uGen huGen_range

  -- build Nonempty S from Nonempty U via the set equality
  haveI : Nonempty S := by
    rcases (inferInstance : Nonempty U) with ⟨u⟩
    have huS : (u.1 : ι → F) ∈ S := by
      have : (u.1 : ι → F) ∈ (S : Set (ι → F)) := by
        simpa [hSU] using u.2
      simpa using this
    exact ⟨⟨u.1, huS⟩⟩

  -- equivalence of sampling spaces
  let e : U ≃ S := by
    simpa [S] using (Equiv.setCongr hSU.symm)

  -- transfer probability along the equivalence
  have hPr_eq :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ] =
        Pr_{let b ← $ᵖ S}[Code.relDistFromCode b RS ≤ δ] := by
    -- use the axiom pr_uniformOfFintype_equiv
    simpa [RS, e] using
      (pr_uniformOfFintype_equiv (α := U) (β := S) e
        (fun b : S => Code.relDistFromCode b RS ≤ δ))

  -- proximity gap theorem for RS codes
  have hPG :=
    ProximityGap.proximity_gap_RSCodes (ι := ι) (F := F)
      (k := Fintype.card U) (t := 1) (deg := deg) (domain := domain)
      (C := C) (δ := δ) (hδ := hδ)

  -- obtain the xor statement for S
  have hXor := hPG S hS_mem

  -- rewrite the predicate to use RS as a set (not via toFinset coercions)
  have hRSset : ((ReedSolomonCode.toFinset domain deg : Finset (ι → F)) : Set (ι → F)) = RS := by
    ext y
    simp [ReedSolomonCode.toFinset, RS]

  have hXor' :
      Xor'
        (Pr_{let x ← $ᵖ S}[Code.relDistFromCode x RS ≤ δ] = (1 : ENNReal))
        (Pr_{let x ← $ᵖ S}[Code.relDistFromCode x RS ≤ δ] ≤ ProximityGap.errorBound δ deg domain) := by
    -- `hXor` is about `δᵣ(x.val, toFinset ..)`; rewrite to our predicate
    simpa [ProximityGap.δ_ε_proximityGap, RS, hRSset] using hXor

  -- main bound on S
  have hMain :
      Pr_{let x ← $ᵖ S}[Code.relDistFromCode x RS ≤ δ]
        ≤ ProximityGap.errorBound δ deg domain := by
    rcases hXor' with hpr1 | hprle
    · -- contradiction from divergence witness
      have hpr1_eq :
          Pr_{let x ← $ᵖ S}[Code.relDistFromCode x RS ≤ δ] = (1 : ENNReal) := hpr1.1

      have hAll : ∀ x : S, Code.relDistFromCode x RS ≤ δ := by
        exact (pr_uniformOfFintype_eq_one_iff_forall (α := S)
          (fun x : S => Code.relDistFromCode x RS ≤ δ)).1 hpr1_eq

      obtain ⟨uStar, huStarU, huStar_eq⟩ :=
        divergence_exists_witness (ι := ι) (F := F)
          (U := (U : Set (ι → F))) (V := RS)

      -- uStar is also in S
      have huStarSset : uStar ∈ (S : Set (ι → F)) := by
        simpa [hSU] using huStarU
      have huStarS : uStar ∈ S := by
        simpa using huStarSset
      let xStar : S := ⟨uStar, huStarS⟩

      have hxStar_le : Code.relDistFromCode xStar RS ≤ δ := hAll xStar

      -- turn hxStar_le into an upper bound on δᵣ'(uStar, RS)
      have hxStar_le' : (Code.relDistFromCode uStar RS : ENNReal) ≤ (δ : ENNReal) := by
        simpa [RS] using hxStar_le

      have hbridge : Code.relDistFromCode uStar RS = (δᵣ'(uStar, RS) : ENNReal) := by
        simpa [RS] using (Code.relDistFromCode'_eq_relDistFromCode (w := uStar) (C := RS))

      have hxStar_le_ratENN : (δᵣ'(uStar, RS) : ENNReal) ≤ (δ : ENNReal) := by
        simpa [hbridge] using hxStar_le'

      have hxStar_le_nnreal : (δᵣ'(uStar, RS) : NNReal) ≤ δ := by
        have h' : ((δᵣ'(uStar, RS) : NNReal) : ENNReal) ≤ (δ : ENNReal) := by
          -- rewrite the NNRat→ENNReal cast through NNReal
          simpa [ENNReal.coe_nnratCast] using hxStar_le_ratENN
        exact (ENNReal.coe_le_coe).1 h'

      have hdiv_le : (DivergenceOfSets.divergence (U : Set (ι → F)) RS : NNReal) ≤ δ := by
        simpa [huStar_eq] using hxStar_le_nnreal

      have hdiv_gt : δ < (DivergenceOfSets.divergence (U : Set (ι → F)) RS : NNReal) := by
        simpa [RS] using hδ_lt

      exact (False.elim (not_le_of_gt hdiv_gt hdiv_le))
    · exact hprle.1

  -- conclude for U
  have :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ] ≤ ProximityGap.errorBound δ deg domain := by
    calc
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ]
          = Pr_{let b ← $ᵖ S}[Code.relDistFromCode b RS ≤ δ] := hPr_eq
      _ ≤ ProximityGap.errorBound δ deg domain := hMain

  simpa [RS] using this


theorem relDistFromCode'_le_divergence {ι : Type} [Fintype ι] [Nonempty ι]
  {F : Type} [Fintype F] [DecidableEq F]
  {U V : Set (ι → F)} [Nonempty V] [Fintype V]
  {u : ι → F} (hu : u ∈ U) :
  δᵣ'(u, V) ≤ DivergenceOfSets.divergence U V := by
  classical
  -- Let d be the relative distance from u to V.
  let d : ℚ≥0 := δᵣ'(u, V)
  have hd_mem : d ∈ DivergenceOfSets.possibleDeltas (U := U) (V := V) := by
    refine ⟨u, hu, ?_⟩
    rfl
  have hne : (DivergenceOfSets.possibleDeltas (U := U) (V := V)).Nonempty := ⟨d, hd_mem⟩
  -- Put a `Fintype` instance on `possibleDeltas U V` (same construction as in `divergence`).
  letI : Fintype (DivergenceOfSets.possibleDeltas (U := U) (V := V)) :=
    @Fintype.ofFinite _ (DivergenceOfSets.finite_possibleDeltas (U := U) (V := V))
  have hd_toFinset : d ∈ (DivergenceOfSets.possibleDeltas (U := U) (V := V)).toFinset := by
    simpa [Set.mem_toFinset] using hd_mem
  have hle_max : d ≤
      (DivergenceOfSets.possibleDeltas (U := U) (V := V)).toFinset.max'
        (Set.toFinset_nonempty.2 hne) := by
    have hle' : d ≤
        (DivergenceOfSets.possibleDeltas (U := U) (V := V)).toFinset.max' ⟨d, hd_toFinset⟩ := by
      exact Finset.le_max' _ _ hd_toFinset
    have hw : (⟨d, hd_toFinset⟩ :
        (DivergenceOfSets.possibleDeltas (U := U) (V := V)).toFinset.Nonempty) =
        Set.toFinset_nonempty.2 hne := by
      exact Subsingleton.elim _ _
    simpa [hw] using hle'
  -- Rewrite `divergence` using the fact that `possibleDeltas` is nonempty and apply the bound.
  simpa [DivergenceOfSets.divergence, hne, d] using hle_max

theorem relHammingDistRange_add_one_div_le_of_lt {ι : Type} [Fintype ι] [Nonempty ι]
  {a b : ℚ≥0}
  (ha : a ∈ Code.relHammingDistRange ι)
  (hb : b ∈ Code.relHammingDistRange ι)
  (hab : a < b) :
  a + (1 / (Fintype.card ι : ℚ≥0)) ≤ b := by
  classical
  rcases ha with ⟨a', ha_le, rfl⟩
  rcases hb with ⟨b', hb_le, rfl⟩
  -- set n = card ι
  have hnpos : (0 : ℚ≥0) < (Fintype.card ι : ℚ≥0) := by
    exact_mod_cast (Fintype.card_pos (α := ι))
  -- cancel the division by n
  have hab' : (a' : ℚ≥0) < (b' : ℚ≥0) := by
    -- hab : (a'/n) < (b'/n)
    exact (div_lt_div_iff_of_pos_right hnpos).1 hab
  have habNat : a' < b' := by
    exact_mod_cast hab'
  have hsucc : a' + 1 ≤ b' := Nat.succ_le_iff.2 habNat
  have hsucc_cast : ((a' : ℚ≥0) + 1) ≤ (b' : ℚ≥0) := by
    -- cast inequality
    -- first cast a'+1
    have : (a' + 1 : ℚ≥0) ≤ (b' : ℚ≥0) := by
      exact_mod_cast hsucc
    -- rewrite cast of a'+1
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hdiv : (((a' : ℚ≥0) + 1) / (Fintype.card ι : ℚ≥0)) ≤ (b' : ℚ≥0) / (Fintype.card ι : ℚ≥0) := by
    exact (div_le_div_iff_of_pos_right hnpos).2 hsucc_cast
  -- rewrite the left hand side using common denominator
  -- (a'/n) + (1/n) = (a'+1)/n
  have hrewrite : (a' : ℚ≥0) / (Fintype.card ι : ℚ≥0) + (1 : ℚ≥0) / (Fintype.card ι : ℚ≥0)
      = ((a' : ℚ≥0) + 1) / (Fintype.card ι : ℚ≥0) := by
    -- use div_add_div_same
    exact (div_add_div_same (a := (a' : ℚ≥0)) (b := (1 : ℚ≥0))
      (c := (Fintype.card ι : ℚ≥0)))
  -- finish
  -- rewrite goal using hrewrite
  --
  -- We avoid simp here to prevent rewriting 1/x as x⁻¹.
  rw [hrewrite]
  exact hdiv


theorem bad_event_iff_relDistFromCode'_le_predecessor {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  (hdiv_pos : 0 < (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal)) :
  let RS : Set (ι → F) := ReedSolomonCode.RScodeSet domain deg
  let δ' : ℚ≥0 := DivergenceOfSets.divergence U RS
  let δ0 : ℚ≥0 := δ' - (1 / (Fintype.card ι : ℚ≥0))
  ∀ u : U, (Code.relDistFromCode (u : ι → F) RS ≠ (δ' : ENNReal)) ↔ δᵣ'(u, RS) ≤ δ0 := by
  classical
  -- unfold the let-bindings in the statement
  dsimp
  intro u
  -- abbreviations
  set RS : Set (ι → F) := ReedSolomonCode.RScodeSet domain deg with hRS
  set δ' : ℚ≥0 := DivergenceOfSets.divergence (U := (U : Set (ι → F))) RS with hδ'
  set δ0 : ℚ≥0 := δ' - (1 / (Fintype.card ι : ℚ≥0)) with hδ0
  -- rewrite goal in terms of the abbreviations
  simp [← hRS, ← hδ', ← hδ0]
  constructor
  · intro hne
    -- bridge between ENNReal and ℚ≥0 distances
    have hrel : Code.relDistFromCode (u : ι → F) RS = (δᵣ'(u, RS) : ENNReal) := by
      simpa using (Code.relDistFromCode'_eq_relDistFromCode (w := (u : ι → F)) (C := RS))
    have hne' : (δᵣ'(u, RS) : ENNReal) ≠ (δ' : ENNReal) := by
      simpa [hrel] using hne
    have hle : δᵣ'(u, RS) ≤ δ' := by
      simpa [hδ'] using
        (relDistFromCode'_le_divergence (U := (U : Set (ι → F))) (V := RS)
          (u := (u : ι → F)) (hu := u.property))
    have hne_q : δᵣ'(u, RS) ≠ δ' := by
      intro hEq
      apply hne'
      simpa [hEq]
    have hlt : δᵣ'(u, RS) < δ' := lt_of_le_of_ne hle hne_q
    -- membership in the relative distance range
    have ha : δᵣ'(u, RS) ∈ Code.relHammingDistRange ι := by
      have hx : δᵣ'(u, RS) ∈ DivergenceOfSets.possibleDeltas (U := (U : Set (ι → F))) RS := by
        refine ⟨(u : ι → F), u.property, rfl⟩
      exact (DivergenceOfSets.possibleDeltas_subset_relHammingDistRange (U := (U : Set (ι → F)))
        (V := RS)) hx
    have hb : δ' ∈ Code.relHammingDistRange ι := by
      -- pick a witness attaining the divergence
      obtain ⟨uStar, huStarU, huStarEq⟩ :=
        divergence_exists_witness (U := (U : Set (ι → F))) (V := RS)
      have hx : δ' ∈ DivergenceOfSets.possibleDeltas (U := (U : Set (ι → F))) RS := by
        refine ⟨uStar, huStarU, ?_⟩
        simpa [hδ'] using huStarEq
      exact (DivergenceOfSets.possibleDeltas_subset_relHammingDistRange (U := (U : Set (ι → F)))
        (V := RS)) hx
    have hadd : δᵣ'(u, RS) + (1 / (Fintype.card ι : ℚ≥0)) ≤ δ' :=
      relHammingDistRange_add_one_div_le_of_lt (ι := ι) (ha := ha) (hb := hb) hlt
    exact le_tsub_of_add_le_right hadd
  · intro hle0
    have hδ'_pos : (0 : ℚ≥0) < δ' := by
      -- use the given positivity statement (as NNReal) and cast back
      have : (0 : NNReal) < (δ' : NNReal) := by
        -- rewrite hdiv_pos in terms of δ'
        simpa [hRS, hδ'] using hdiv_pos
      exact_mod_cast this
    have h_one_div_pos : (0 : ℚ≥0) < (1 / (Fintype.card ι : ℚ≥0)) := by
      have hcard_pos : (0 : ℚ≥0) < (Fintype.card ι : ℚ≥0) := by
        exact_mod_cast (Fintype.card_pos (α := ι))
      exact (one_div_pos.2 hcard_pos)
    have hδ0_lt : δ0 < δ' := by
      -- δ0 = δ' - 1/n
      simpa [hδ0] using (tsub_lt_self hδ'_pos h_one_div_pos)
    have hlt : δᵣ'(u, RS) < δ' := lt_of_le_of_lt hle0 hδ0_lt
    have hltNN : (δᵣ'(u, RS) : NNReal) < (δ' : NNReal) := by
      exact_mod_cast hlt
    have hltENN' : ((δᵣ'(u, RS) : NNReal) : ENNReal) < ((δ' : NNReal) : ENNReal) :=
      (ENNReal.coe_lt_coe).2 hltNN
    have hltENN : (δᵣ'(u, RS) : ENNReal) < (δ' : ENNReal) := by
      simpa [ENNReal.coe_nnratCast] using hltENN'
    have hneENN : (δᵣ'(u, RS) : ENNReal) ≠ (δ' : ENNReal) := ne_of_lt hltENN
    have hrel : Code.relDistFromCode (u : ι → F) RS = (δᵣ'(u, RS) : ENNReal) := by
      simpa using (Code.relDistFromCode'_eq_relDistFromCode (w := (u : ι → F)) (C := RS))
    -- rewrite back
    simpa [hrel] using hneENN

theorem concentration_bounds {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {deg : ℕ} [NeZero deg] {domain : ι ↪ F}
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  (hdiv_pos : 0 < (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal))
  (hdiv_lt : (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal) <
    1 - ReedSolomonCode.sqrtRate deg domain) :
  let δ' := DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg)
  Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (ReedSolomonCode.RScodeSet domain deg) ≠ δ']
    ≤ ProximityGap.errorBound δ' deg domain := by
  classical
  -- unfold the `let` in the goal
  dsimp

  -- abbreviations
  let RS : Set (ι → F) := ReedSolomonCode.RScodeSet domain deg
  let δq : ℚ≥0 := DivergenceOfSets.divergence U RS
  let δ0q : ℚ≥0 := δq - (1 / (Fintype.card ι : ℚ≥0))

  -- bad event rewritten as the predecessor event (in ℚ≥0)
  have hbad' :
      ∀ u : U,
        (Code.relDistFromCode (u : ι → F) RS ≠ (δq : ENNReal)) ↔ δᵣ'(u, RS) ≤ δ0q := by
    simpa [RS, δq, δ0q] using
      (bad_event_iff_relDistFromCode'_le_predecessor (ι := ι) (F := F) (deg := deg)
        (domain := domain) (U := U) hdiv_pos)

  -- convert `δᵣ' ≤ δ0q` into a statement about `Code.relDistFromCode ≤ δ0`
  have hbad :
      ∀ u : U,
        (Code.relDistFromCode (u : ι → F) RS ≠ (δq : ENNReal)) ↔
          Code.relDistFromCode (u : ι → F) RS ≤ (δ0q : NNReal) := by
    intro u
    constructor
    · intro hne
      have hle_q : δᵣ'(u, RS) ≤ δ0q := (hbad' u).1 hne
      have hle_nn : (δᵣ'(u, RS) : NNReal) ≤ (δ0q : NNReal) := by
        exact_mod_cast hle_q
      have hle_enn : (δᵣ'(u, RS) : ENNReal) ≤ (δ0q : ENNReal) := by
        simpa [ENNReal.coe_NNRat_coe_NNReal] using (ENNReal.coe_le_coe.2 hle_nn)
      have hEq : Code.relDistFromCode (u : ι → F) RS = (δᵣ'(u, RS) : ENNReal) := by
        simpa [RS] using
          (Code.relDistFromCode'_eq_relDistFromCode (w := (u : ι → F)) (C := RS))
      have : Code.relDistFromCode (u : ι → F) RS ≤ (δ0q : ENNReal) := by
        simpa [hEq] using hle_enn
      simpa using this
    · intro hle
      have hEq : Code.relDistFromCode (u : ι → F) RS = (δᵣ'(u, RS) : ENNReal) := by
        simpa [RS] using
          (Code.relDistFromCode'_eq_relDistFromCode (w := (u : ι → F)) (C := RS))
      have hle' : (δᵣ'(u, RS) : ENNReal) ≤ (δ0q : ENNReal) := by
        simpa [hEq] using hle
      have hle_nn : (δᵣ'(u, RS) : NNReal) ≤ (δ0q : NNReal) := by
        have : ((δᵣ'(u, RS) : NNReal) : ENNReal) ≤ ((δ0q : NNReal) : ENNReal) := by
          simpa [ENNReal.coe_NNRat_coe_NNReal] using hle'
        exact (ENNReal.coe_le_coe.1 this)
      have hle_q : δᵣ'(u, RS) ≤ δ0q := by
        exact_mod_cast hle_nn
      exact (hbad' u).2 hle_q

  -- rewrite the probability using pointwise equivalence
  have hPr :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≠ (δq : ENNReal)] =
        Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≤ (δ0q : NNReal)] := by
    simp [ProbabilityTheory.prStx, hbad]

  -- helper: δq < 1 - sqrtRate
  have hδq_lt : (δq : NNReal) < 1 - ReedSolomonCode.sqrtRate deg domain := by
    simpa [RS, δq] using hdiv_lt

  have hδ0_le : (δ0q : NNReal) ≤ (δq : NNReal) := by
    have hδ0_le_q : δ0q ≤ δq := by
      simpa [δ0q] using (tsub_le_self : δq - (1 / (Fintype.card ι : ℚ≥0)) ≤ δq)
    exact_mod_cast hδ0_le_q

  have hδ0_lt : (δ0q : NNReal) < (δq : NNReal) := by
    -- strict inequality in ℚ≥0, then cast
    have hδq_pos : (0 : ℚ≥0) < δq := by
      exact_mod_cast hdiv_pos
    have hone_pos : (0 : ℚ≥0) < (1 / (Fintype.card ι : ℚ≥0)) := by
      have hcard_pos : 0 < (Fintype.card ι : ℚ≥0) := by
        exact_mod_cast (Fintype.card_pos (α := ι))
      simpa using (one_div_pos.2 hcard_pos)
    have hlt_q : δ0q < δq := by
      simpa [δ0q] using
        (tsub_lt_self (a := δq) (b := (1 / (Fintype.card ι : ℚ≥0))) hδq_pos hone_pos)
    exact_mod_cast hlt_q

  -- proximity gap bound at δ0
  have hgap0 :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ (δ0q : NNReal)]
        ≤ ProximityGap.errorBound (δ0q : NNReal) deg domain :=
    proximity_gap_bound_affineSubspace (ι := ι) (F := F) (deg := deg) (domain := domain)
      (U := U) (δ := (δ0q : NNReal))
      (hδ := le_trans hδ0_le (le_of_lt hδq_lt))
      (hδ_lt := by simpa [δq] using hδ0_lt)

  -- monotonicity of probability w.r.t. predicate implication (uniform measure)
  have pr_mono {δ₁ δ₂ : NNReal} (hδ : δ₁ ≤ δ₂) :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ₁] ≤
        Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ₂] := by
    classical
    refine
      pr_uniformOfFintype_mono_of_imp (α := U)
        (P := fun u : U => Code.relDistFromCode u RS ≤ δ₁)
        (Q := fun u : U => Code.relDistFromCode u RS ≤ δ₂) ?_
    intro u hu
    have hδ' : (δ₁ : ENNReal) ≤ (δ₂ : ENNReal) := by
      exact_mod_cast hδ
    exact le_trans hu hδ'

  -- Johnson radius
  let τ : NNReal := (1 - (LinearCode.rate (ReedSolomon.code domain deg) : NNReal)) / 2

  by_cases hjohn : τ < (δ0q : NNReal)
  · -- Johnson regime: compare error bounds directly
    have hmono :
        ProximityGap.errorBound (δ0q : NNReal) deg domain ≤
          ProximityGap.errorBound (δq : NNReal) deg domain := by
      apply errorBound_mono_on_johnson_interval (ι := ι) (F := F) (deg := deg) (domain := domain)
        (δ₁ := (δ0q : NNReal)) (δ₂ := (δq : NNReal))
      · exact hδ0_le
      · simpa [τ] using hjohn
      · simpa [RS, δq] using hdiv_lt

    -- finish by chaining
    calc
      Pr_{let u ← $ᵖ U}[
          Code.relDistFromCode (u : ι → F) (ReedSolomonCode.RScodeSet domain deg) ≠
            DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg)]
          = Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≠ (δq : ENNReal)] := by
              simp [RS, δq]
      _ = Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≤ (δ0q : NNReal)] := hPr
      _ ≤ ProximityGap.errorBound (δ0q : NNReal) deg domain := by
            simpa using hgap0
      _ ≤ ProximityGap.errorBound (δq : NNReal) deg domain := by
            exact_mod_cast hmono
      _ =
          ProximityGap.errorBound
            (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal)
            deg domain := by
            simp [RS, δq]

  · -- below Johnson radius: split on whether δq is also below
    have hδ0_le_τ : (δ0q : NNReal) ≤ τ := le_of_not_gt hjohn
    by_cases hδq_le_τ : (δq : NNReal) ≤ τ
    · -- both δ0 and δq in the first branch, so `errorBound` is constant
      have hδ0_in : (δ0q : NNReal) ∈ Set.Icc (0 : NNReal) τ := by
        refine ⟨bot_le, hδ0_le_τ⟩
      have hδq_in : (δq : NNReal) ∈ Set.Icc (0 : NNReal) τ := by
        refine ⟨bot_le, hδq_le_τ⟩
      have herr_eq :
          ProximityGap.errorBound (δ0q : NNReal) deg domain =
            ProximityGap.errorBound (δq : NNReal) deg domain := by
        simp [ProximityGap.errorBound, hδ0_in, hδq_in, τ]
      calc
        Pr_{let u ← $ᵖ U}[
            Code.relDistFromCode (u : ι → F) (ReedSolomonCode.RScodeSet domain deg) ≠
              DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg)]
            = Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≠ (δq : ENNReal)] := by
                simp [RS, δq]
        _ = Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≤ (δ0q : NNReal)] := hPr
        _ ≤ ProximityGap.errorBound (δ0q : NNReal) deg domain := by
              simpa using hgap0
        _ = ProximityGap.errorBound (δq : NNReal) deg domain := by
              simpa [herr_eq]
        _ =
            ProximityGap.errorBound
              (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal)
              deg domain := by
              simp [RS, δq]

    · -- straddle case: pick an intermediate δ₁ in the Johnson interval
      have hτ_lt_δq : τ < (δq : NNReal) := lt_of_not_ge hδq_le_τ
      let δ1 : NNReal := (τ + (δq : NNReal)) / 2
      have htwo_pos : (0 : NNReal) < (2 : NNReal) := by
        norm_num
      have hτ_lt_δ1 : τ < δ1 := by
        -- τ < (τ + δq)/2 since τ < δq
        have hmul : τ * (2 : NNReal) < τ + (δq : NNReal) := by
          have : τ + τ < τ + (δq : NNReal) := add_lt_add_left hτ_lt_δq τ
          simpa [mul_two] using this
        simpa [δ1] using (lt_div_iff₀ htwo_pos).2 hmul
      have hδ1_lt_δq : δ1 < (δq : NNReal) := by
        have hmul : τ + (δq : NNReal) < (δq : NNReal) * (2 : NNReal) := by
          have : τ + (δq : NNReal) < (δq : NNReal) + (δq : NNReal) :=
            add_lt_add_right hτ_lt_δq (δq : NNReal)
          simpa [mul_two] using this
        simpa [δ1] using (div_lt_iff₀ htwo_pos).2 hmul
      have hδ0_le_δ1 : (δ0q : NNReal) ≤ δ1 :=
        le_trans hδ0_le_τ (le_of_lt hτ_lt_δ1)

      have hPr_le :
          Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ (δ0q : NNReal)] ≤
            Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ1] :=
        pr_mono (δ₁ := (δ0q : NNReal)) (δ₂ := δ1) hδ0_le_δ1

      have hgap1 :
          Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ1] ≤
            ProximityGap.errorBound δ1 deg domain :=
        proximity_gap_bound_affineSubspace (ι := ι) (F := F) (deg := deg) (domain := domain)
          (U := U) (δ := δ1)
          (hδ := le_trans (le_of_lt hδ1_lt_δq) (le_of_lt hδq_lt))
          (hδ_lt := by simpa [δq] using hδ1_lt_δq)

      have hmono :
          ProximityGap.errorBound δ1 deg domain ≤ ProximityGap.errorBound (δq : NNReal) deg domain := by
        apply errorBound_mono_on_johnson_interval (ι := ι) (F := F) (deg := deg) (domain := domain)
          (δ₁ := δ1) (δ₂ := (δq : NNReal))
        · exact le_of_lt hδ1_lt_δq
        · -- τ < δ1
          simpa [τ] using hτ_lt_δ1
        · simpa [RS, δq] using hdiv_lt

      calc
        Pr_{let u ← $ᵖ U}[
            Code.relDistFromCode (u : ι → F) (ReedSolomonCode.RScodeSet domain deg) ≠
              DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg)]
            = Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≠ (δq : ENNReal)] := by
                simp [RS, δq]
        _ = Pr_{let u ← $ᵖ U}[Code.relDistFromCode (u : ι → F) RS ≤ (δ0q : NNReal)] := hPr
        _ ≤ Pr_{let u ← $ᵖ U}[Code.relDistFromCode u RS ≤ δ1] := by
              -- use monotonicity under implication
              exact le_trans (le_rfl) (by
                -- convert hPr_le to the exact form we need
                simpa using hPr_le)
        _ ≤ ProximityGap.errorBound δ1 deg domain := by
              simpa using hgap1
        _ ≤ ProximityGap.errorBound (δq : NNReal) deg domain := by
              exact_mod_cast hmono
        _ =
            ProximityGap.errorBound
              (DivergenceOfSets.divergence U (ReedSolomonCode.RScodeSet domain deg) : NNReal)
              deg domain := by
              simp [RS, δq]

