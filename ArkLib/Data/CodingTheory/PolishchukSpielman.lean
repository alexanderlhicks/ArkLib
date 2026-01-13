/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Divisibility.Units
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import ArkLib.Data.Polynomial.Prelims
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Degree.Domain


open Polynomial.Bivariate Polynomial


open scoped BigOperators
open Polynomial
open Polynomial.Bivariate
open Matrix

theorem PS_bx_lt_nx {b_x b_y : ℕ} {n_x n_y : ℕ+}
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_x < (n_x : ℕ) := by
  have hby_nonneg : (0 : ℚ) ≤ (b_y : ℚ) / (n_y : ℚ) := by
    have hnum : (0 : ℚ) ≤ (b_y : ℚ) := by
      exact_mod_cast (Nat.zero_le b_y)
    have hden : (0 : ℚ) ≤ (n_y : ℚ) := by
      have hden' : (0 : ℚ) < (n_y : ℚ) := by
        exact_mod_cast (PNat.pos n_y)
      exact le_of_lt hden'
    exact div_nonneg hnum hden
  have hb : (b_x : ℚ) / (n_x : ℚ) < 1 := by
    have hsum : (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) < 1 := by
      simpa [gt_iff_lt] using h_le_1
    have h' : (b_x : ℚ) / (n_x : ℚ) < 1 - (b_y : ℚ) / (n_y : ℚ) := by
      linarith
    have hle : 1 - (b_y : ℚ) / (n_y : ℚ) ≤ 1 := by
      linarith [hby_nonneg]
    exact lt_of_lt_of_le h' hle
  have hnx_pos : (0 : ℚ) < (n_x : ℚ) := by
    exact_mod_cast (PNat.pos n_x)
  have hnx_ne : (n_x : ℚ) ≠ 0 := by
    exact ne_of_gt hnx_pos
  have hx : (b_x : ℚ) < (n_x : ℚ) := by
    have hmul := mul_lt_mul_of_pos_right hb hnx_pos
    -- (b_x / n_x) * n_x < 1 * n_x
    simpa [div_mul_cancel₀, hnx_ne, one_mul] using hmul
  exact_mod_cast hx

theorem PS_by_lt_ny {b_x b_y : ℕ} {n_x n_y : ℕ+}
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) : b_y < (n_y : ℕ) := by
  have hsum : (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) < 1 := by
    exact h_le_1
  have hx_nonneg : 0 ≤ (b_x : ℚ) / (n_x : ℚ) := by
    have hb : (0 : ℚ) ≤ (b_x : ℚ) := by
      exact_mod_cast (Nat.zero_le b_x)
    have hn : (0 : ℚ) ≤ (n_x : ℚ) := by
      have hn' : (0 : ℚ) < (n_x : ℚ) := by
        exact_mod_cast n_x.pos
      exact le_of_lt hn'
    exact div_nonneg hb hn
  have hy_le : (b_y : ℚ) / (n_y : ℚ) ≤ (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) := by
    exact le_add_of_nonneg_left hx_nonneg
  have hy_lt_one : (b_y : ℚ) / (n_y : ℚ) < 1 := by
    exact lt_of_le_of_lt hy_le hsum
  have hn_y : (0 : ℚ) < (n_y : ℚ) := by
    exact_mod_cast n_y.pos
  have hn_y_ne : (n_y : ℚ) ≠ 0 := by
    exact ne_of_gt hn_y
  have hy_lt : (b_y : ℚ) < (n_y : ℚ) := by
    have hmul : (b_y : ℚ) / (n_y : ℚ) * (n_y : ℚ) < (1 : ℚ) * (n_y : ℚ) :=
      mul_lt_mul_of_pos_right hy_lt_one hn_y
    -- simplify both sides
    simpa [div_mul_cancel₀, hn_y_ne] using hmul
  exact_mod_cast hy_lt


theorem PS_card_evalX_eq_zero_le_degreeX {F : Type} [Field F] [DecidableEq F]
  (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
  (P.filter (fun x => Polynomial.Bivariate.evalX x A = 0)).card ≤ Polynomial.Bivariate.degreeX A := by
  classical
  have hcoeff_test (x : F) (j : ℕ) : (Polynomial.Bivariate.evalX x A).coeff j = (A.coeff j).eval x := by
    simp [Polynomial.Bivariate.evalX, Polynomial.coeff]

  have hsupp : A.support.Nonempty := (Polynomial.support_nonempty).2 hA
  obtain ⟨j0, hj0mem, hj0sup⟩ :=
    Finset.exists_mem_eq_sup A.support hsupp (fun n => (A.coeff n).natDegree)
  have hj0deg : (A.coeff j0).natDegree = Polynomial.Bivariate.degreeX A := by
    simpa [Polynomial.Bivariate.degreeX] using hj0sup.symm
  have hc0 : A.coeff j0 ≠ 0 := (Polynomial.mem_support_iff).1 hj0mem
  let S : Finset F := P.filter (fun x => Polynomial.Bivariate.evalX x A = 0)
  have hsub : S.val ⊆ (A.coeff j0).roots := by
    intro x hx
    have hxS : x ∈ S := by
      simpa [S] using hx
    have hxEval : Polynomial.Bivariate.evalX x A = 0 := (Finset.mem_filter.1 hxS).2
    have hxcoeff : (A.coeff j0).eval x = 0 := by
      have := congrArg (fun q : Polynomial F => q.coeff j0) hxEval
      simpa [hcoeff_test, Polynomial.coeff_zero] using this
    have hxroot : Polynomial.IsRoot (A.coeff j0) x := by
      simpa [Polynomial.IsRoot] using hxcoeff
    exact (Polynomial.mem_roots hc0).2 hxroot
  have hcard : S.card ≤ (A.coeff j0).natDegree := by
    simpa using (Polynomial.card_le_degree_of_subset_roots (p := A.coeff j0) (Z := S) hsub)
  have : S.card ≤ Polynomial.Bivariate.degreeX A := by
    -- hcard : S.card ≤ (A.coeff j0).natDegree and hj0deg : (A.coeff j0).natDegree = degreeX A
    simpa [hj0deg] using hcard
  simpa [S] using this


theorem PS_card_evalY_eq_zero_le_natDegreeY {F : Type} [Field F] [DecidableEq F]
  (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
  (P.filter (fun y => Polynomial.Bivariate.evalY y A = 0)).card ≤ Polynomial.Bivariate.natDegreeY A := by
  classical
  -- Let `bad` be the subset of `P` on which `A` vanishes after evaluating in `Y`.
  set bad : Finset F := P.filter (fun y => Polynomial.Bivariate.evalY y A = 0)
  -- Consider the corresponding set of constant polynomials `C y : F[X]`.
  set Z : Finset F[X] := bad.image (fun y : F => (Polynomial.C y : F[X]))

  have hcard : bad.card = Z.card := by
    -- `C` is injective, so taking images preserves cardinality.
    have h :=
      (Finset.card_image_of_injective (s := bad)
        (f := fun y : F => (Polynomial.C y : F[X]))
        (by
          intro a b hab
          exact Polynomial.C_injective hab))
    -- `h : Z.card = bad.card`
    simpa [Z] using h.symm

  -- Show `Z` is contained in the multiset of roots of `A` (viewed as a polynomial in `Y`).
  have hZ : (Z.1 : Multiset F[X]) ⊆ A.roots := by
    intro z hz
    -- unpack membership in the image
    have hz' : z ∈ Z := hz
    rcases Finset.mem_image.1 hz' with ⟨y, hybad, rfl⟩
    have hy : Polynomial.Bivariate.evalY y A = 0 := by
      -- membership in the filter gives the defining property
      exact (show y ∈ P ∧ Polynomial.Bivariate.evalY y A = 0 by
        simpa [bad] using hybad).2
    -- `hy` says `C y` is a root of `A`.
    have : IsRoot A (Polynomial.C y : F[X]) := by
      -- `evalY` is just `Polynomial.eval (C y)`.
      simpa [Polynomial.Bivariate.evalY, Polynomial.IsRoot] using hy
    -- therefore it lies in `A.roots`
    exact (Polynomial.mem_roots hA).2 this

  -- Apply the standard bound on the number of distinct roots.
  have hZcard : Z.card ≤ A.natDegree := by
    simpa using (Polynomial.card_le_degree_of_subset_roots (p := A) (Z := Z) hZ)

  -- Translate back to the original statement.
  -- `natDegreeY` is just `natDegree`.
  simpa [Polynomial.Bivariate.natDegreeY, bad, hcard] using hZcard

theorem PS_coeff_mul_monomial_ite {R : Type} [Semiring R]
  (A : R[X]) (j i : ℕ) (r : R) :
  (A * Polynomial.monomial j r).coeff i =
    if j ≤ i then A.coeff (i - j) * r else 0 := by
  classical
  simpa [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow',
    Polynomial.coeff_mul_C]

theorem PS_coeff_mul_sum_monomial {R : Type} [CommRing R]
  (A : R[X]) (m n : ℕ) (hm : A.natDegree ≤ m)
  (c : Fin n → R) (i : ℕ) :
  (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j))).coeff i =
    ∑ j : Fin n,
      if (j : ℕ) ≤ i ∧ i ≤ (j : ℕ) + m
      then A.coeff (i - (j : ℕ)) * c j else 0 := by
  classical
  -- Work with explicit `Finset.univ` so we can use `Finset.mul_sum` and `Polynomial.finset_sum_coeff`.
  have hdeg : ∀ N : ℕ, m < N → A.coeff N = 0 :=
    (Polynomial.natDegree_le_iff_coeff_eq_zero (p := A) (n := m)).1 hm

  -- Expand the product over the sum.
  -- First rewrite the coefficient of the product as a sum of coefficients.
  --
  -- We keep the sum written as `∑ j : Fin n, ...` but `simp` will unfold it to a `Finset.univ` sum
  -- when applying `Finset.mul_sum`/`Polynomial.finset_sum_coeff`.
  --
  -- Start by pushing multiplication inside the sum.
  --
  -- LHS
  --   (A * (∑ j, monomial j (c j))).coeff i
  -- = (∑ j, (A * monomial j (c j))).coeff i
  -- = ∑ j, (A * monomial j (c j)).coeff i
  --
  -- and then rewrite each coefficient via `PS_coeff_mul_monomial_ite`.
  
  -- Convert to a `Finset` sum and take coefficients.
  --
  -- `simp` turns `∑ j : Fin n, ...` into `∑ j ∈ Finset.univ, ...` as needed.
  
  -- Main computation
  --
  -- After this `simp`, the goal becomes a statement about a sum over `Finset.univ`.
  simp [Finset.mul_sum, Polynomial.finset_sum_coeff, PS_coeff_mul_monomial_ite, hdeg] 
  
  -- Now we just need to refine the condition `j ≤ i` to `j ≤ i ∧ i ≤ j + m`.
  -- We do this by analyzing each `j`.
  
  -- The remaining goal is a sum congruence; solve it termwise.
  refine Finset.sum_congr rfl ?_
  intro j hj
  -- `hj : j ∈ Finset.univ` is irrelevant.
  by_cases hji : (j : ℕ) ≤ i
  · by_cases him : i ≤ (j : ℕ) + m
    · simp [hji, him]
    · have hjm : (j : ℕ) + m < i := Nat.lt_of_not_ge him
      have hm' : m < i - (j : ℕ) := by
        -- from `m + j < i`, infer `m < i - j`
        have : m + (j : ℕ) < i := by simpa [Nat.add_comm] using hjm
        exact lt_tsub_of_add_lt_right this
      have hcoeff0 : A.coeff (i - (j : ℕ)) = 0 := hdeg (i - (j : ℕ)) hm'
      simp [hji, him, hcoeff0]
  · simp [hji]


theorem PS_degreeX_swap {F : Type} [CommRing F]
  (f : F[X][Y]) :
  Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap f) =
    Polynomial.Bivariate.natDegreeY f := by
  classical
  -- A coefficient-level description of `swap`.
  have hcoeff :
      ∀ (g : F[X][Y]) (i j : ℕ),
        Polynomial.Bivariate.coeff (Polynomial.Bivariate.swap g) i j =
          Polynomial.Bivariate.coeff g j i := by
    intro g i j
    induction g using Polynomial.induction_on' with
    | add p q hp hq =>
        -- rewrite the IHs so they apply after unfolding `Bivariate.coeff`
        have hp' : ((Polynomial.Bivariate.swap p).coeff j).coeff i = (p.coeff i).coeff j := by
          simpa [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply] using hp
        have hq' : ((Polynomial.Bivariate.swap q).coeff j).coeff i = (q.coeff i).coeff j := by
          simpa [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply] using hq
        simp [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply, hp', hq', add_comm,
          add_left_comm, add_assoc]
    | monomial n a =>
        -- inner induction on the coefficient `a : F[X]`
        induction a using Polynomial.induction_on' with
        | add p q hp hq =>
            have hp' : ((Polynomial.Bivariate.swap ((monomial n) p)).coeff j).coeff i =
                (((monomial n) p).coeff i).coeff j := by
              simpa [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply] using hp
            have hq' : ((Polynomial.Bivariate.swap ((monomial n) q)).coeff j).coeff i =
                (((monomial n) q).coeff i).coeff j := by
              simpa [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply] using hq
            simp [Polynomial.Bivariate.coeff, Polynomial.monomial_add, -Polynomial.Bivariate.swap_apply,
              hp', hq', add_comm, add_left_comm, add_assoc]
        | monomial m r =>
            -- now `g = monomial n (monomial m r)`
            by_cases hi : n = i
            · subst hi
              by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hj]
            · by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hi]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hi, hj]

  -- Unfold the ArkLib degree definitions.
  unfold Polynomial.Bivariate.degreeX Polynomial.Bivariate.natDegreeY

  by_cases hf : f = 0
  · subst hf
    simp
  · -- main (nonzero) case
    apply le_antisymm
    · -- `degreeX (swap f) ≤ natDegree f`
      refine Finset.sup_le_iff.2 ?_
      intro n hn
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have hfm : f.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hm
      have hmn : ((Polynomial.Bivariate.swap f).coeff n).coeff m = (f.coeff m).coeff n := by
        simpa [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply] using (hcoeff f m n)
      rw [hmn]
      simp [hfm]
    · -- `natDegree f ≤ degreeX (swap f)`
      have hNmem : natDegree f ∈ f.support :=
        Polynomial.natDegree_mem_support_of_nonzero hf
      have hcoeffN0 : f.coeff (natDegree f) ≠ 0 := (Polynomial.mem_support_iff.mp hNmem)
      let n : ℕ := (f.coeff (natDegree f)).natDegree
      have hnmem : n ∈ (f.coeff (natDegree f)).support := by
        simpa [n] using Polynomial.natDegree_mem_support_of_nonzero hcoeffN0
      have hcoeffn : (f.coeff (natDegree f)).coeff n ≠ 0 := (Polynomial.mem_support_iff.mp hnmem)
      have hEq : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) =
          (f.coeff (natDegree f)).coeff n := by
        simpa [Polynomial.Bivariate.coeff, n, -Polynomial.Bivariate.swap_apply] using
          (hcoeff f (natDegree f) n)
      have hswapCoeff : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) ≠ 0 := by
        simpa [hEq, -Polynomial.Bivariate.swap_apply] using hcoeffn
      have hNle_natDeg : natDegree f ≤ ((Polynomial.Bivariate.swap f).coeff n).natDegree :=
        Polynomial.le_natDegree_of_ne_zero hswapCoeff
      have hcoeff_nonzero : (Polynomial.Bivariate.swap f).coeff n ≠ 0 := by
        intro hzero
        apply hswapCoeff
        rw [hzero]
        simp
      have hn_support : n ∈ (Polynomial.Bivariate.swap f).support :=
        (Polynomial.mem_support_iff.2 hcoeff_nonzero)
      have hn_le_degX :
          ((Polynomial.Bivariate.swap f).coeff n).natDegree ≤
            (Polynomial.Bivariate.swap f).support.sup
              (fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) :=
        Finset.le_sup (f := fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) hn_support
      exact le_trans hNle_natDeg hn_le_degX

theorem PS_descend_evalX {F : Type} [Field F] [DecidableEq F]
  {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
  (x : F) (hx : Polynomial.Bivariate.evalX x G ≠ 0) (q : F[X])
  (h : Polynomial.Bivariate.evalX x B = q * Polynomial.Bivariate.evalX x A) :
  Polynomial.Bivariate.evalX x B1 = q * Polynomial.Bivariate.evalX x A1 := by
  classical
  -- First show that `evalX` is the same as the usual coefficient map.
  have evalX_eq_map (f : F[X][Y]) : Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
    ext n
    simp [Polynomial.Bivariate.evalX, Polynomial.toFinsupp_apply]
  -- use this lemma to rewrite the hypothesis and goal
  have hmap : (B.map (Polynomial.evalRingHom x)) = q * (A.map (Polynomial.evalRingHom x)) := by
    simpa [evalX_eq_map] using h
  -- now substitute the factorizations of `A` and `B`
  have hmap' : ((G * B1).map (Polynomial.evalRingHom x)) = q * ((G * A1).map (Polynomial.evalRingHom x)) := by
    simpa [hB, hA] using hmap
  -- expand the map over multiplication
  have hmap'' : (G.map (Polynomial.evalRingHom x)) * (B1.map (Polynomial.evalRingHom x))
      = q * ((G.map (Polynomial.evalRingHom x)) * (A1.map (Polynomial.evalRingHom x))) := by
    simpa [mul_assoc] using hmap'
  -- cancel the nonzero factor
  have hg' : (G.map (Polynomial.evalRingHom x)) ≠ 0 := by
    simpa [evalX_eq_map] using hx
  have hcancel : (B1.map (Polynomial.evalRingHom x)) = q * (A1.map (Polynomial.evalRingHom x)) := by
    apply mul_left_cancel₀ hg'
    -- rearrange `hmap''` so the common factor is on the left
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmap''
  -- rewrite back to `evalX`
  simpa [evalX_eq_map] using hcancel

theorem PS_descend_evalY {F : Type} [Field F] [DecidableEq F]
  {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
  (y : F) (hy : Polynomial.Bivariate.evalY y G ≠ 0) (q : F[X])
  (h : Polynomial.Bivariate.evalY y B = q * Polynomial.Bivariate.evalY y A) :
  Polynomial.Bivariate.evalY y B1 = q * Polynomial.Bivariate.evalY y A1 := by
  have h' : Polynomial.Bivariate.evalY y (G * B1) = q * Polynomial.Bivariate.evalY y (G * A1) := by
    simpa [hB, hA] using h
  have h'' :
      Polynomial.Bivariate.evalY y G * Polynomial.Bivariate.evalY y B1 =
        q * (Polynomial.Bivariate.evalY y G * Polynomial.Bivariate.evalY y A1) := by
    simpa [Polynomial.Bivariate.evalY, Polynomial.eval_mul, mul_assoc] using h'
  apply mul_left_cancel₀ hy
  calc
    Polynomial.Bivariate.evalY y G * Polynomial.Bivariate.evalY y B1 =
        q * (Polynomial.Bivariate.evalY y G * Polynomial.Bivariate.evalY y A1) := h''
    _ = Polynomial.Bivariate.evalY y G * (q * Polynomial.Bivariate.evalY y A1) := by
      rw [← mul_assoc, mul_comm q (Polynomial.Bivariate.evalY y G), mul_assoc]


theorem PS_evalX_eq_map {F : Type} [CommSemiring F]
  (x : F) (f : F[X][Y]) :
  Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
  classical
  ext n
  simp [Polynomial.Bivariate.evalX, Polynomial.toFinsupp_apply]


theorem PS_evalY_eq_evalX_swap {F : Type} [CommRing F]
  (y : F) (f : F[X][Y]) :
  Polynomial.Bivariate.evalY y f =
    Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
  classical

  -- Use the same `F[X]`-algebra structure on `F[X]` as in `Polynomial.Bivariate.aveal_eq_map_swap`.
  -- (This is *not* the default `Algebra.id` instance.)
  letI : Algebra F[X] F[X] := Polynomial.algebra (R := F) (A := F)

  -- `evalX` is coefficientwise evaluation in the inner variable, i.e. coefficient-map by `evalRingHom`.
  have evalX_eq_map (g : F[X][Y]) :
      Polynomial.Bivariate.evalX y g = g.map (Polynomial.evalRingHom y) := by
    ext n
    simp [Polynomial.Bivariate.evalX, Polynomial.coeff_map, Polynomial.toFinsupp_apply]

  -- Convert `aeval (C y)` (using the `Polynomial.algebra` instance above) into `eval (C y)`.
  have eval_eq_aeval : Polynomial.eval (Polynomial.C y) f = aeval (Polynomial.C y) f := by
    -- show the relevant `algebraMap F[X] F[X]` is the identity
    have halg : (algebraMap F[X] F[X]) = RingHom.id (F[X]) := by
      -- `algebraMap` for `Polynomial.algebra` is `mapRingHom (algebraMap F F)`.
      simpa [Polynomial.mapRingHom_id] using
        (Polynomial.algebraMap_def (R := F) (A := F))
    -- now unfold `eval`/`aeval`
    simp [Polynomial.eval, Polynomial.aeval_def, halg]

  -- Rewrite the RHS of `aveal_eq_map_swap` into a `map` by `evalRingHom`.
  have mapAlgHom_eq_map :
      Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f)
        = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
    -- first: `mapAlgHom` coerces to `map`
    have h1 :
        Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f) =
          (Polynomial.Bivariate.swap f).map (((aeval y : F[X] →ₐ[F] F) : F[X] →+* F)) := by
      simpa using
        (congrArg (fun g => g (Polynomial.Bivariate.swap f))
          (Polynomial.coe_mapAlgHom (f := (aeval y : F[X] →ₐ[F] F))))
    -- second: coerce `aeval y` to `evalRingHom y`
    have h2 : (((aeval y : F[X] →ₐ[F] F) : F[X] →+* F)) = Polynomial.evalRingHom y := by
      simpa using (Polynomial.coe_aeval_eq_evalRingHom (R := F) (x := y))
    simpa [h2] using h1

  have hmain : Polynomial.Bivariate.evalY y f = Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
    -- start from Mathlib's `aveal_eq_map_swap`
    have hswap :=
      (Polynomial.Bivariate.aveal_eq_map_swap (R := F) (A := F) (x := y) (p := f))
    -- rewrite `evalY` via `eval_eq_aeval`, and the RHS via `mapAlgHom_eq_map` / `evalX_eq_map`
    calc
      Polynomial.Bivariate.evalY y f
          = Polynomial.eval (Polynomial.C y) f := by
              rfl
      _ = aeval (Polynomial.C y) f := eval_eq_aeval
      _ = Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f) := hswap
      _ = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := mapAlgHom_eq_map
      _ = Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
            simpa using (evalX_eq_map (g := Polynomial.Bivariate.swap f)).symm

  exact hmain

theorem PS_exists_P_of_degreeX_eq_zero_natDegreeY_eq_zero {F : Type} [Field F]
  {A B : F[X][Y]} (hA0 : A ≠ 0)
  (hdegX : Polynomial.Bivariate.degreeX A = 0)
  (hdegY : Polynomial.Bivariate.natDegreeY A = 0)
  : ∃ P : F[X][Y], B = P * A := by
  classical
  have hdegY' : A.natDegree = 0 := by
    simpa [Polynomial.Bivariate.natDegreeY] using hdegY
  rcases (Polynomial.natDegree_eq_zero).1 hdegY' with ⟨a0, ha0⟩

  have ha0ne : a0 ≠ 0 := by
    intro ha0z
    apply hA0
    calc
      A = C a0 := ha0.symm
      _ = 0 := by simpa [ha0z]

  have hdegX' : Polynomial.Bivariate.degreeX (C a0 : F[X][Y]) = 0 := by
    simpa [ha0.symm] using hdegX

  have ha0_natdeg : a0.natDegree = 0 := by
    simpa [Polynomial.Bivariate.degreeX, Polynomial.support_C ha0ne] using hdegX'

  rcases (Polynomial.natDegree_eq_zero).1 ha0_natdeg with ⟨a, ha⟩

  have ha_ne : a ≠ 0 := by
    intro haz
    apply hA0
    calc
      A = C a0 := ha0.symm
      _ = C (C a) := by simpa [ha.symm]
      _ = 0 := by simpa [haz]

  have hA : A = C (C a) := by
    calc
      A = C a0 := ha0.symm
      _ = C (C a) := by simpa [ha.symm]

  have hinner : (C a⁻¹ : F[X]) * (C a : F[X]) = C (a⁻¹ * a) := by
    simpa using (Polynomial.C_mul (a := (a⁻¹ : F)) (b := (a : F))).symm

  have hCa : (C (C a⁻¹) : F[X][Y]) * C (C a) = 1 := by
    calc
      (C (C a⁻¹) : F[X][Y]) * C (C a) = C ((C a⁻¹ : F[X]) * (C a : F[X])) := by
        simpa using
          (Polynomial.C_mul (a := (C a⁻¹ : F[X])) (b := (C a : F[X]))).symm
      _ = C (C (a⁻¹ * a)) := by
        -- avoid simp loop between `C_mul` and `hinner`
        rw [hinner]
      _ = 1 := by
        simp [ha_ne]

  refine ⟨B * C (C a⁻¹), ?_⟩
  -- use that `C (C a)` is a unit with inverse `C (C a⁻¹)`
  calc
    B = B * 1 := by simp
    _ = B * ((C (C a⁻¹) : F[X][Y]) * C (C a)) := by
      rw [←hCa]
    _ = (B * C (C a⁻¹)) * C (C a) := by
      simpa using (mul_assoc B (C (C a⁻¹) : F[X][Y]) (C (C a) : F[X][Y])).symm
    _ = (B * C (C a⁻¹)) * A := by
      simpa [hA]


theorem PS_exists_Qx_of_cancel {F : Type} [Field F] [DecidableEq F]
  (a_x : ℕ) (n_x : ℕ+)
  {A B P : F[X][Y]}
  (hA : A ≠ 0)
  (hBA : B = P * A)
  (P_x : Finset F) (h_card_Px : n_x ≤ P_x.card)
  (quot_Y : F → F[X])
  (h_quot_Y : ∀ x ∈ P_x,
    Polynomial.Bivariate.evalX x B = (quot_Y x) * (Polynomial.Bivariate.evalX x A))
  (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
  : ∃ Q_x : Finset F,
      Q_x.card ≥ (n_x : ℕ) - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Polynomial.Bivariate.evalX x P = quot_Y x := by
  classical
  let Q_x : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0)
  refine ⟨Q_x, ?_, ?_, ?_⟩
  · -- cardinality bound
    let Z_x : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A = 0)
    have hZdeg : Z_x.card ≤ Polynomial.Bivariate.degreeX A := by
      simpa [Z_x] using
        (PS_card_evalX_eq_zero_le_degreeX (A := A) (hA := hA) (P := P_x))
    have hZle : Z_x.card ≤ a_x := le_trans hZdeg h_f_degX
    have hsplit : Z_x.card + Q_x.card = P_x.card := by
      simpa [Z_x, Q_x] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_x)
          (p := fun x : F => Polynomial.Bivariate.evalX x A = 0))
    have hP_eq : P_x.card = Z_x.card + Q_x.card := hsplit.symm
    have hPsub : P_x.card - a_x ≤ Q_x.card := by
      have hle : P_x.card - a_x ≤ P_x.card - Z_x.card := by
        -- subtraction is antitone in the subtrahend
        exact tsub_le_tsub_left hZle P_x.card
      have hP_minus : P_x.card - Z_x.card = Q_x.card := by
        calc
          P_x.card - Z_x.card = (Z_x.card + Q_x.card) - Z_x.card := by
            simpa [hP_eq]
          _ = Q_x.card := Nat.add_sub_cancel_left _ _
      simpa [hP_minus] using hle
    have hnsub : (n_x : ℕ) - a_x ≤ P_x.card - a_x :=
      Nat.sub_le_sub_right h_card_Px a_x
    exact le_trans hnsub hPsub
  · -- subset
    intro x hx
    have hx' : x ∈ P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0) := by
      simpa [Q_x] using hx
    exact (Finset.mem_filter.mp hx').1
  · -- agreement by cancellation
    intro x hx
    have hx' : x ∈ P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0) := by
      simpa [Q_x] using hx
    have hxP : x ∈ P_x := (Finset.mem_filter.mp hx').1
    have hxA : Polynomial.Bivariate.evalX x A ≠ 0 := (Finset.mem_filter.mp hx').2

    -- relate evalX to `Polynomial.map` so we can use `map_mul`
    have evalX_eq_map (x : F) (f : F[X][Y]) :
        Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
      ext n
      simp [Polynomial.Bivariate.evalX, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
        Polynomial.toFinsupp_apply]

    have evalX_mul (x : F) (f g : F[X][Y]) :
        Polynomial.Bivariate.evalX x (f * g) =
          Polynomial.Bivariate.evalX x f * Polynomial.Bivariate.evalX x g := by
      simp [evalX_eq_map, Polynomial.map_mul]

    have hBAx : Polynomial.Bivariate.evalX x B =
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
      calc
        Polynomial.Bivariate.evalX x B = Polynomial.Bivariate.evalX x (P * A) := by
          simpa using congrArg (Polynomial.Bivariate.evalX x) hBA
        _ = Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
          simpa using evalX_mul x P A

    have hquot : Polynomial.Bivariate.evalX x B =
        (quot_Y x) * Polynomial.Bivariate.evalX x A :=
      h_quot_Y x hxP

    have hcancel_eq :
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A =
          (quot_Y x) * Polynomial.Bivariate.evalX x A := by
      calc
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A =
            Polynomial.Bivariate.evalX x B := by
          simpa using hBAx.symm
        _ = (quot_Y x) * Polynomial.Bivariate.evalX x A := hquot

    exact mul_right_cancel₀ hxA hcancel_eq

theorem PS_exists_Qy_of_cancel {F : Type} [Field F] [DecidableEq F]
  (a_y : ℕ) (n_y : ℕ+)
  {A B P : F[X][Y]}
  (hA : A ≠ 0)
  (hBA : B = P * A)
  (P_y : Finset F) (h_card_Py : n_y ≤ P_y.card)
  (quot_X : F → F[X])
  (h_quot_X : ∀ y ∈ P_y,
    Polynomial.Bivariate.evalY y B = (quot_X y) * (Polynomial.Bivariate.evalY y A))
  (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A)
  : ∃ Q_y : Finset F,
      Q_y.card ≥ (n_y : ℕ) - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Polynomial.Bivariate.evalY y P = quot_X y := by
  classical
  let Q_y : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A ≠ 0)
  refine ⟨Q_y, ?_, ?_, ?_⟩
  · -- cardinality bound
    let bad : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A = 0)
    have hsum : bad.card + Q_y.card = P_y.card := by
      simpa [bad, Q_y] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_y)
          (p := fun y : F => Polynomial.Bivariate.evalY y A = 0))
    have hbad : bad.card ≤ a_y := by
      have h1 : bad.card ≤ Polynomial.Bivariate.natDegreeY A :=
        PS_card_evalY_eq_zero_le_natDegreeY A hA P_y
      exact le_trans h1 h_f_degY
    have hny : (n_y : ℕ) ≤ P_y.card := by
      simpa using h_card_Py
    have h1 : (n_y : ℕ) - a_y ≤ P_y.card - a_y := Nat.sub_le_sub_right hny a_y
    have h2 : P_y.card - a_y ≤ P_y.card - bad.card := Nat.sub_le_sub_left hbad P_y.card
    have hsub : P_y.card - bad.card = Q_y.card := by
      -- (bad + Q) - bad = Q
      simpa [hsum] using (add_tsub_cancel_left bad.card Q_y.card)
    have h12 : (n_y : ℕ) - a_y ≤ P_y.card - bad.card := le_trans h1 h2
    have : (n_y : ℕ) - a_y ≤ Q_y.card := by
      simpa [hsub] using h12
    exact this
  · -- subset
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  · -- evaluation property
    intro y hy
    have hyP : y ∈ P_y := (Finset.mem_filter.mp hy).1
    have hyA : Polynomial.Bivariate.evalY y A ≠ 0 := (Finset.mem_filter.mp hy).2
    have hquot : Polynomial.Bivariate.evalY y B = (quot_X y) * Polynomial.Bivariate.evalY y A :=
      h_quot_X y hyP
    have hquot' : Polynomial.Bivariate.evalY y (P * A) = (quot_X y) * Polynomial.Bivariate.evalY y A := by
      simpa [hBA] using hquot
    have hmul : Polynomial.Bivariate.evalY y (P * A) =
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A := by
      simp [Polynomial.Bivariate.evalY]
    have hcancel :
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A =
          (quot_X y) * Polynomial.Bivariate.evalY y A := by
      calc
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A =
            Polynomial.Bivariate.evalY y (P * A) := by simpa using hmul.symm
        _ = (quot_X y) * Polynomial.Bivariate.evalY y A := hquot'
    exact mul_right_cancel₀ hyA hcancel

theorem PS_exists_x_preserve_natDegreeY {F : Type} [Field F] [DecidableEq F]
  (B : F[X][Y]) (hB : B ≠ 0) (P_x : Finset F)
  (hcard : P_x.card > Polynomial.Bivariate.degreeX B) :
  ∃ x ∈ P_x, (Polynomial.Bivariate.evalX x B).natDegree = Polynomial.Bivariate.natDegreeY B := by
  classical
  let d : ℕ := Polynomial.Bivariate.natDegreeY B
  let p : F[X] := Polynomial.Bivariate.leadingCoeffY B
  have hp0 : p ≠ 0 := by
    -- leading coefficient in Y is nonzero since B ≠ 0
    simpa [p] using (Polynomial.Bivariate.leadingCoeffY_ne_zero (f := B)).2 hB
  have hp_deg : p.natDegree ≤ Polynomial.Bivariate.degreeX B := by
    -- `degreeX` is the sup of the X-degrees of all Y-coefficients
    have hdmem : B.natDegree ∈ B.support := Polynomial.natDegree_mem_support_of_nonzero hB
    have : (B.coeff B.natDegree).natDegree ≤ B.support.sup (fun n => (B.coeff n).natDegree) :=
      Finset.le_sup (f := fun n => (B.coeff n).natDegree) hdmem
    simpa [p, Polynomial.Bivariate.leadingCoeffY, Polynomial.Bivariate.degreeX] using this
  have hlt : p.natDegree < P_x.card := lt_of_le_of_lt hp_deg hcard
  have hx : ∃ x ∈ P_x, p.eval x ≠ 0 := by
    by_contra h
    have hall : ∀ x ∈ P_x, p.eval x = 0 := by
      intro x hx
      by_contra hxne
      exact h ⟨x, hx, hxne⟩
    have hsub : P_x.val ⊆ p.roots := by
      intro x hxval
      have hxP : x ∈ P_x := (Finset.mem_def).2 hxval
      have hxroot : Polynomial.IsRoot p x := by
        -- `IsRoot` means `eval x p = 0`
        simpa [Polynomial.IsRoot] using hall x hxP
      exact (Polynomial.mem_roots hp0).2 hxroot
    have hle : P_x.card ≤ p.natDegree := by
      simpa using (Polynomial.card_le_degree_of_subset_roots (p := p) (Z := P_x) hsub)
    exact (not_lt_of_ge hle) hlt
  rcases hx with ⟨x, hxPx, hxne⟩
  refine ⟨x, hxPx, ?_⟩
  have hnat_le : (Polynomial.Bivariate.evalX x B).natDegree ≤ Polynomial.Bivariate.natDegreeY B := by
    -- coefficients above `natDegreeY B` vanish
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hBN : B.coeff N = 0 := by
      -- because `N` is above the Y-degree of `B`
      have : B.natDegree < N := by
        simpa [Polynomial.Bivariate.natDegreeY] using hN
      exact Polynomial.coeff_eq_zero_of_natDegree_lt this
    have hBN' : B.toFinsupp N = 0 := by
      simpa [Polynomial.coeff] using hBN
    simp [Polynomial.Bivariate.evalX, hBN']
  have hcoeff : (Polynomial.Bivariate.evalX x B).coeff (Polynomial.Bivariate.natDegreeY B) ≠ 0 := by
    -- the top coefficient is `p.eval x`
    simpa [d, p, Polynomial.Bivariate.evalX, Polynomial.Bivariate.leadingCoeffY,
      Polynomial.Bivariate.natDegreeY] using hxne
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnat_le hcoeff


theorem PS_exists_y_preserve_degreeX {F : Type} [Field F] [DecidableEq F]
  (B : F[X][Y]) (hB : B ≠ 0) (P_y : Finset F)
  (hcard : P_y.card > Polynomial.Bivariate.natDegreeY B) :
  ∃ y ∈ P_y, (Polynomial.Bivariate.evalY y B).natDegree = Polynomial.Bivariate.degreeX B := by
  classical
  -- Let `d` be the maximal `X`-degree of a coefficient of `B`.
  set d : ℕ := Polynomial.Bivariate.degreeX B with hd
  -- Let `g` be the coefficient of `X^d` viewed as a univariate polynomial in `Y`.
  set g : F[X] := B.sum (fun j p => Polynomial.monomial j (p.coeff d)) with hg

  -- Pick a `Y`-index where the `X`-degree of the coefficient polynomial reaches `d`.
  have hBsup_ne : B.support.Nonempty := (Polynomial.support_nonempty.2 hB)
  obtain ⟨j0, hj0_mem, hj0_deg⟩ :=
    Finset.exists_mem_eq_sup B.support hBsup_ne (fun n => (B.coeff n).natDegree)

  have hj0_deg' : (B.coeff j0).natDegree = d := by
    simpa [Polynomial.Bivariate.degreeX, hd] using hj0_deg.symm

  have hj0_coeff_ne : (B.coeff j0).coeff d ≠ 0 := by
    have hj0_ne : B.coeff j0 ≠ 0 := (Polynomial.mem_support_iff.1 hj0_mem)
    have hlead : (B.coeff j0).leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero.2 hj0_ne)
    simpa [Polynomial.leadingCoeff, hj0_deg'] using hlead

  -- Hence `g` is nonzero.
  have hg_ne : g ≠ 0 := by
    have hg_coeff : g.coeff j0 = (B.coeff j0).coeff d := by
      rw [hg]
      simp [Polynomial.coeff_sum, Polynomial.sum_def, Polynomial.coeff_monomial,
        Finset.sum_ite_eq, hj0_mem]
    intro hzero
    have : g.coeff j0 = 0 := by simpa [hzero]
    exact hj0_coeff_ne (by simpa [hg_coeff] using this)

  -- Degree bound: `g.natDegree ≤ natDegreeY B`.
  have hg_natDegree_le : g.natDegree ≤ Polynomial.Bivariate.natDegreeY B := by
    simp [Polynomial.Bivariate.natDegreeY]
    rw [hg, Polynomial.sum_def]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := B.support)
        (f := fun j => Polynomial.monomial j ((B.coeff j).coeff d))
        (n := B.natDegree)
        ?_
    intro j hj
    exact le_trans
      (Polynomial.natDegree_monomial_le (a := (B.coeff j).coeff d) (m := j))
      (Polynomial.le_natDegree_of_mem_supp (p := B) j hj)

  -- Since `P_y.card > natDegreeY B`, we also have `g.natDegree < P_y.card`.
  have hcard_g : g.natDegree < P_y.card := lt_of_le_of_lt hg_natDegree_le hcard

  -- Choose `y ∈ P_y` with `g.eval y ≠ 0`.
  have hy_exists : ∃ y ∈ P_y, g.eval y ≠ 0 := by
    by_contra h
    have heval : ∀ y ∈ P_y, g.eval y = 0 := by
      intro y hy
      by_contra hne
      exact h ⟨y, hy, hne⟩
    have : g = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g P_y heval (by simpa using hcard_g)
    exact hg_ne this

  rcases hy_exists with ⟨y, hyP, hgy_ne⟩
  refine ⟨y, hyP, ?_⟩

  -- First, show `natDegree (evalY y B) ≤ d`.
  have hdeg_le : (Polynomial.Bivariate.evalY y B).natDegree ≤ d := by
    have heval : Polynomial.Bivariate.evalY y B =
        ∑ j ∈ B.support, B.coeff j * (Polynomial.C y : F[X]) ^ j := by
      simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [heval]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := B.support)
        (f := fun j => B.coeff j * (Polynomial.C y : F[X]) ^ j)
        (n := d)
        ?_
    intro j hj
    have hj_le : (B.coeff j).natDegree ≤ d := by
      have : (B.coeff j).natDegree ≤ B.support.sup (fun n => (B.coeff n).natDegree) :=
        Finset.le_sup (s := B.support) (f := fun n => (B.coeff n).natDegree) hj
      simpa [Polynomial.Bivariate.degreeX, hd] using this
    have hmul : (B.coeff j * (Polynomial.C y : F[X]) ^ j).natDegree ≤ (B.coeff j).natDegree := by
      simpa using (Polynomial.natDegree_mul_C_le (f := B.coeff j) (a := y ^ j))
    exact le_trans hmul hj_le

  -- Compute the coefficient of `X^d` in `evalY y B`.
  have hcoeff_evalY :
      (Polynomial.Bivariate.evalY y B).coeff d =
        ∑ j ∈ B.support, (B.coeff j).coeff d * y ^ j := by
    have heval : Polynomial.Bivariate.evalY y B =
        ∑ j ∈ B.support, B.coeff j * (Polynomial.C y : F[X]) ^ j := by
      simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [heval]
    rw [Polynomial.finset_sum_coeff (s := B.support)
      (f := fun j => B.coeff j * (Polynomial.C y : F[X]) ^ j) (n := d)]
    refine Finset.sum_congr rfl ?_
    intro j hj
    -- Use `coeff_mul_C` after rewriting `C (y^j)` as `(C y)^j`.
    simpa [Polynomial.C_pow] using
      (Polynomial.coeff_mul_C (p := B.coeff j) (n := d) (a := y ^ j))

  -- Compute `g.eval y` as the same sum.
  have hcoeff_g : g.eval y = ∑ j ∈ B.support, (B.coeff j).coeff d * y ^ j := by
    rw [hg, Polynomial.sum_def]
    -- Evaluate termwise.
    rw [Polynomial.eval_finset_sum]
    simp [Polynomial.eval_monomial]

  have hcoeff_eq : (Polynomial.Bivariate.evalY y B).coeff d = g.eval y := by
    simpa [hcoeff_evalY, hcoeff_g]

  have hcoeff_ne : (Polynomial.Bivariate.evalY y B).coeff d ≠ 0 := by
    simpa [hcoeff_eq] using hgy_ne

  have hnat : (Polynomial.Bivariate.evalY y B).natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg_le hcoeff_ne

  simpa [hd] using hnat

theorem PS_degree_bounds_of_mul {F : Type} [Field F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  {A B P : F[X][Y]}
  (hA : A ≠ 0)
  (hBA : B = P * A)
  (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
  (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
  (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A)
  (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧
      Polynomial.Bivariate.evalY y B = (quot_X y) * (Polynomial.Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧
      Polynomial.Bivariate.evalX x B = (quot_Y x) * (Polynomial.Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  : Polynomial.Bivariate.degreeX P ≤ b_x - a_x ∧ Polynomial.Bivariate.natDegreeY P ≤ b_y - a_y := by
  classical
  letI : DecidableEq F := Classical.decEq F

  by_cases hB0 : B = 0
  · have hPA : P * A = 0 := by
      calc
        P * A = B := by simpa [hBA]
        _ = 0 := hB0
    have hP0 : P = 0 := by
      rcases mul_eq_zero.mp hPA with hP0 | hA0
      · exact hP0
      · exfalso
        exact hA hA0
    subst hP0
    constructor <;> simp [Polynomial.Bivariate.degreeX, Polynomial.Bivariate.natDegreeY]
  · have hB : B ≠ 0 := hB0
    have hP : P ≠ 0 := by
      intro hP0
      apply hB
      simp [hBA, hP0]

    -- helper: evalX multiplicativity via map
    have evalX_eq_map (a : F) (f : F[X][Y]) : Polynomial.Bivariate.evalX a f = f.map (Polynomial.evalRingHom a) := by
      ext n
      simp [Polynomial.Bivariate.evalX, Polynomial.coeff]
      simpa [Polynomial.coe_evalRingHom, Polynomial.coeff] using
        (Polynomial.coeff_map (p := f) (f := Polynomial.evalRingHom a) n).symm

    have evalX_mul (a : F) (f g : F[X][Y]) :
        Polynomial.Bivariate.evalX a (f * g) = Polynomial.Bivariate.evalX a f * Polynomial.Bivariate.evalX a g := by
      simp [evalX_eq_map, Polynomial.map_mul]

    -- filtered set in Y
    let Py0 : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A = 0)
    let Py' : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y A ≠ 0)

    have hPy0_le : Py0.card ≤ Polynomial.Bivariate.natDegreeY A := by
      simpa [Py0] using
        PS_card_evalY_eq_zero_le_natDegreeY (A := A) (hA := hA) (P := P_y)

    have hcard_part : Py0.card + Py'.card = P_y.card := by
      simpa [Py0, Py'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_y)
          (p := fun y : F => Polynomial.Bivariate.evalY y A = 0))

    have hPy'_ge : P_y.card - Polynomial.Bivariate.natDegreeY A ≤ Py'.card := by
      have hsub : P_y.card - Polynomial.Bivariate.natDegreeY A ≤ P_y.card - Py0.card :=
        tsub_le_tsub_left hPy0_le P_y.card
      have hPy0_sub : Py'.card = P_y.card - Py0.card := by
        -- subtract Py0.card from partition equation
        have htmp := congrArg (fun t => t - Py0.card) hcard_part
        simpa [Nat.add_sub_cancel_left] using htmp
      -- rewrite
      simpa [hPy0_sub] using hsub

    have hby_lt_ny : b_y < (n_y : ℕ) :=
      PS_by_lt_ny (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
    have hby_lt_card : b_y < P_y.card := lt_of_lt_of_le hby_lt_ny h_card_Py

    have hdegA_le_by : Polynomial.Bivariate.natDegreeY A ≤ b_y := le_trans h_f_degY h_by_ge_ay

    have hdegY :
        Polynomial.Bivariate.natDegreeY B =
          Polynomial.Bivariate.natDegreeY P + Polynomial.Bivariate.natDegreeY A := by
      calc
        Polynomial.Bivariate.natDegreeY B = Polynomial.Bivariate.natDegreeY (P * A) := by
          simpa [hBA]
        _ = Polynomial.Bivariate.natDegreeY P + Polynomial.Bivariate.natDegreeY A := by
          simpa using (Polynomial.Bivariate.degreeY_mul (F := F) P A hP hA)

    have hsumY :
        Polynomial.Bivariate.natDegreeY P + Polynomial.Bivariate.natDegreeY A ≤ b_y := by
      -- rewrite natDegreeY B in h_g_degY
      have hBN : Polynomial.Bivariate.natDegreeY B ≤ b_y := h_g_degY
      simpa [hdegY] using hBN

    have hnatDegY_P_le :
        Polynomial.Bivariate.natDegreeY P ≤ b_y - Polynomial.Bivariate.natDegreeY A :=
      le_tsub_of_add_le_right hsumY

    have hbsubY : b_y - Polynomial.Bivariate.natDegreeY A < P_y.card - Polynomial.Bivariate.natDegreeY A :=
      tsub_lt_tsub_right_of_le hdegA_le_by hby_lt_card

    have hPy'_card : Py'.card > Polynomial.Bivariate.natDegreeY P := by
      have hlt : Polynomial.Bivariate.natDegreeY P < P_y.card - Polynomial.Bivariate.natDegreeY A :=
        lt_of_le_of_lt hnatDegY_P_le hbsubY
      have hlt' : Polynomial.Bivariate.natDegreeY P < Py'.card := lt_of_lt_of_le hlt hPy'_ge
      exact hlt'

    -- choose y preserving degreeX
    rcases PS_exists_y_preserve_degreeX (F := F) (B := P) (hB := hP) (P_y := Py') hPy'_card with
      ⟨y, hyPy', hydegX⟩

    have hyP_y : y ∈ P_y := (Finset.mem_filter.mp hyPy').1
    have hyA0 : Polynomial.Bivariate.evalY y A ≠ 0 := (Finset.mem_filter.mp hyPy').2

    have hquotX_deg : (quot_X y).natDegree ≤ b_x - a_x := (h_quot_X y hyP_y).1
    have hquotX_eq : Polynomial.Bivariate.evalY y B = (quot_X y) * Polynomial.Bivariate.evalY y A :=
      (h_quot_X y hyP_y).2

    have hBA_evalY :
        Polynomial.Bivariate.evalY y B =
          Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A := by
      calc
        Polynomial.Bivariate.evalY y B = Polynomial.Bivariate.evalY y (P * A) := by
          simpa [hBA]
        _ = Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A := by
          -- evalY is Polynomial.eval
          simp [Polynomial.Bivariate.evalY, Polynomial.eval_mul]

    have hEvalY_P_eq_quot : Polynomial.Bivariate.evalY y P = quot_X y := by
      apply mul_right_cancel₀ hyA0
      -- cancel the common right factor
      calc
        Polynomial.Bivariate.evalY y P * Polynomial.Bivariate.evalY y A = Polynomial.Bivariate.evalY y B := by
          simpa [hBA_evalY]
        _ = quot_X y * Polynomial.Bivariate.evalY y A := hquotX_eq

    have hdegX_P_le : Polynomial.Bivariate.degreeX P ≤ b_x - a_x := by
      -- hydegX : (evalY y P).natDegree = degreeX P
      have hdegX' : Polynomial.Bivariate.degreeX P = (Polynomial.Bivariate.evalY y P).natDegree := hydegX.symm
      rw [hdegX']
      simpa [hEvalY_P_eq_quot] using hquotX_deg

    -- Now the X-direction
    let Px0 : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A = 0)
    let Px' : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x A ≠ 0)

    have hPx0_le : Px0.card ≤ Polynomial.Bivariate.degreeX A := by
      simpa [Px0] using PS_card_evalX_eq_zero_le_degreeX (A := A) (hA := hA) (P := P_x)

    have hcard_partX : Px0.card + Px'.card = P_x.card := by
      simpa [Px0, Px'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_x)
          (p := fun x : F => Polynomial.Bivariate.evalX x A = 0))

    have hPx'_ge : P_x.card - Polynomial.Bivariate.degreeX A ≤ Px'.card := by
      have hsub : P_x.card - Polynomial.Bivariate.degreeX A ≤ P_x.card - Px0.card :=
        tsub_le_tsub_left hPx0_le P_x.card
      have hPx0_sub : Px'.card = P_x.card - Px0.card := by
        have htmp := congrArg (fun t => t - Px0.card) hcard_partX
        simpa [Nat.add_sub_cancel_left] using htmp
      simpa [hPx0_sub] using hsub

    have hbx_lt_nx : b_x < (n_x : ℕ) :=
      PS_bx_lt_nx (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
    have hbx_lt_card : b_x < P_x.card := lt_of_lt_of_le hbx_lt_nx h_card_Px

    have hdegX_A_le_bx : Polynomial.Bivariate.degreeX A ≤ b_x := by
      -- degreeX A ≤ a_x ≤ b_x
      exact le_trans (show Polynomial.Bivariate.degreeX A ≤ a_x from h_f_degX) h_bx_ge_ax

    have hbsubX : b_x - Polynomial.Bivariate.degreeX A < P_x.card - Polynomial.Bivariate.degreeX A :=
      tsub_lt_tsub_right_of_le hdegX_A_le_bx hbx_lt_card

    have hdegX_P_le' : Polynomial.Bivariate.degreeX P ≤ b_x - Polynomial.Bivariate.degreeX A := by
      -- degreeX P ≤ b_x - a_x ≤ b_x - degreeX A
      have h1 : b_x - a_x ≤ b_x - Polynomial.Bivariate.degreeX A :=
        tsub_le_tsub_left (show Polynomial.Bivariate.degreeX A ≤ a_x from h_f_degX) b_x
      exact le_trans hdegX_P_le h1

    have hPx'_card : Px'.card > Polynomial.Bivariate.degreeX P := by
      have hlt : Polynomial.Bivariate.degreeX P < P_x.card - Polynomial.Bivariate.degreeX A :=
        lt_of_le_of_lt hdegX_P_le' hbsubX
      have hlt' : Polynomial.Bivariate.degreeX P < Px'.card := lt_of_lt_of_le hlt hPx'_ge
      exact hlt'

    rcases PS_exists_x_preserve_natDegreeY (F := F) (B := P) (hB := hP) (P_x := Px') hPx'_card with
      ⟨x, hxPx', hxdegY⟩

    have hxP_x : x ∈ P_x := (Finset.mem_filter.mp hxPx').1
    have hxA0 : Polynomial.Bivariate.evalX x A ≠ 0 := (Finset.mem_filter.mp hxPx').2

    have hquotY_deg : (quot_Y x).natDegree ≤ b_y - a_y := (h_quot_Y x hxP_x).1
    have hquotY_eq : Polynomial.Bivariate.evalX x B = (quot_Y x) * Polynomial.Bivariate.evalX x A :=
      (h_quot_Y x hxP_x).2

    have hBA_evalX :
        Polynomial.Bivariate.evalX x B =
          Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
      calc
        Polynomial.Bivariate.evalX x B = Polynomial.Bivariate.evalX x (P * A) := by
          simpa [hBA]
        _ = Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A := by
          simpa [evalX_mul]

    have hEvalX_P_eq_quot : Polynomial.Bivariate.evalX x P = quot_Y x := by
      apply mul_right_cancel₀ hxA0
      calc
        Polynomial.Bivariate.evalX x P * Polynomial.Bivariate.evalX x A = Polynomial.Bivariate.evalX x B := by
          simpa [hBA_evalX]
        _ = quot_Y x * Polynomial.Bivariate.evalX x A := hquotY_eq

    have hdegY_P_le : Polynomial.Bivariate.natDegreeY P ≤ b_y - a_y := by
      -- hxdegY : (evalX x P).natDegree = natDegreeY P
      have hdegY' : Polynomial.Bivariate.natDegreeY P = (Polynomial.Bivariate.evalX x P).natDegree := hxdegY.symm
      rw [hdegY']
      simpa [hEvalX_P_eq_quot] using hquotY_deg

    exact ⟨hdegX_P_le, hdegY_P_le⟩


theorem PS_gcd_decompose {F : Type} [Field F]
  {A B : F[X][Y]} (hA : A ≠ 0) (hB : B ≠ 0) :
  ∃ G A1 B1 : F[X][Y],
    A = G * A1 ∧ B = G * B1 ∧ IsRelPrime A1 B1 ∧ A1 ≠ 0 ∧ B1 ≠ 0 := by
  classical
  let G : F[X][Y] := gcd A B
  have hGA : G ∣ A := by
    simpa [G] using (gcd_dvd_left A B)
  have hGB : G ∣ B := by
    simpa [G] using (gcd_dvd_right A B)
  rcases hGA with ⟨A1, hAfac⟩
  rcases hGB with ⟨B1, hBfac⟩
  refine ⟨G, A1, B1, ?_⟩

  have hG0 : G ≠ 0 := by
    intro hG0
    apply hA
    simpa [hAfac, hG0] using (rfl : A = 0)

  have hA1 : A1 ≠ 0 := by
    intro hA10
    apply hA
    simpa [hAfac, hA10] using (rfl : A = 0)

  have hB1 : B1 ≠ 0 := by
    intro hB10
    apply hB
    simpa [hBfac, hB10] using (rfl : B = 0)

  have hnorm : normalize G = G := by
    simpa [G] using (normalize_gcd A B)

  have hgcdAB : gcd A B = normalize G * gcd A1 B1 := by
    calc
      gcd A B = gcd (G * A1) (G * B1) := by
        simpa [hAfac, hBfac]
      _ = normalize G * gcd A1 B1 := by
        simpa [mul_assoc] using (gcd_mul_left G A1 B1)

  have hEq : G = normalize G * gcd A1 B1 := by
    simpa [G] using hgcdAB

  have hEq' : G = G * gcd A1 B1 := by
    simpa [hnorm] using hEq

  have hgcd_eq_one : gcd A1 B1 = 1 := by
    have hmul : G * 1 = G * gcd A1 B1 := by
      simpa [mul_one] using hEq'
    exact (mul_left_cancel₀ hG0 hmul).symm

  have hgcd_unit : IsUnit (gcd A1 B1) := by
    rw [hgcd_eq_one]
    exact isUnit_one

  have hrel : IsRelPrime A1 B1 :=
    (gcd_isUnit_iff_isRelPrime).1 hgcd_unit

  exact ⟨hAfac, hBfac, hrel, hA1, hB1⟩

theorem PS_isRelPrime_swap {F : Type} [CommRing F] {A B : F[X][Y]}
  (h : IsRelPrime A B) :
  IsRelPrime (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) := by
  classical
  let f : F[X][Y] ≃+* F[X][Y] := (Polynomial.Bivariate.swap (R := F)).toRingEquiv
  -- reduce to the definition and pull everything back along the equivalence
  refine fun d hdA hdB => ?_
  have hdA' : f.symm d ∣ A :=
    (map_dvd_iff (f := f)).1 (by simpa [f] using hdA)
  have hdB' : f.symm d ∣ B :=
    (map_dvd_iff (f := f)).1 (by simpa [f] using hdB)
  have hunit : IsUnit (f.symm d) := h hdA' hdB'
  have : IsUnit (f (f.symm d)) := (f.toRingHom).isUnit_map hunit
  simpa [f] using this

theorem PS_natDegreeY_swap {F : Type} [CommRing F]
  (f : F[X][Y]) :
  Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
    Polynomial.Bivariate.degreeX f := by
  classical
  have h := PS_degreeX_swap (F := F) (f := Polynomial.Bivariate.swap f)
  have hs : Polynomial.Bivariate.swap (R := F) (Polynomial.Bivariate.swap f) = f := by
    simpa using (Polynomial.Bivariate.swap (R := F)).left_inv f
  have h' :
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
        Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) := by
    simpa using h.symm
  have hdeg :
      Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) =
        Polynomial.Bivariate.degreeX f := by
    simpa using congrArg Polynomial.Bivariate.degreeX hs
  exact h'.trans hdeg

theorem PS_natDegree_mul_X_pow_le {F : Type} [Semiring F] [Nontrivial F]
  (Q : F[X]) {m n : ℕ} (j : Fin m)
  (hmn : m ≤ n) (hQdeg : Q.natDegree ≤ n - m) :
  (Q * X ^ (j : ℕ)).natDegree ≤ n - 1 := by
  classical
  have hdeg : (Q * X ^ (j : ℕ)).natDegree ≤ (n - m) + (j : ℕ) := by
    refine Polynomial.natDegree_mul_le_of_le (p := Q) (q := (X : F[X]) ^ (j : ℕ)) hQdeg ?_
    simpa using (Polynomial.natDegree_X_pow_le (R := F) (j : ℕ))
  have hlt : (n - m) + (j : ℕ) < n := by
    have hj : (j : ℕ) < m := j.isLt
    have hlt' : (n - m) + (j : ℕ) < (n - m) + m :=
      Nat.add_lt_add_left hj (n - m)
    simpa [Nat.sub_add_cancel hmn] using hlt'
  have hle : (n - m) + (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt hlt
  exact le_trans hdeg hle

theorem PS_natDegree_resultant_le {F : Type} [Field F]
  (A B : F[X][Y]) (m n : ℕ)
  (hm : Polynomial.Bivariate.natDegreeY A ≤ m)
  (hn : Polynomial.Bivariate.natDegreeY B ≤ n) :
  (Polynomial.resultant A B m n).natDegree ≤
    m * (Polynomial.Bivariate.degreeX B) + n * (Polynomial.Bivariate.degreeX A) := by
  classical
  -- Work with the Sylvester matrix whose determinant defines the resultant.
  let M : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := Polynomial.sylvester A B m n

  -- Every coefficient of `A` has `X`-degree bounded by `degreeX A`.
  have hAcoeff : ∀ k : ℕ, (A.coeff k).natDegree ≤ Polynomial.Bivariate.degreeX A := by
    intro k
    classical
    unfold Polynomial.Bivariate.degreeX
    by_cases hk : k ∈ A.support
    ·
      -- use the definition of `Finset.sup`
      simpa using
        (Finset.le_sup (s := A.support) (f := fun t : ℕ => (A.coeff t).natDegree) hk)
    ·
      have hk0 : A.coeff k = 0 := (Polynomial.notMem_support_iff.mp hk)
      simp [hk0]

  -- Every coefficient of `B` has `X`-degree bounded by `degreeX B`.
  have hBcoeff : ∀ k : ℕ, (B.coeff k).natDegree ≤ Polynomial.Bivariate.degreeX B := by
    intro k
    classical
    unfold Polynomial.Bivariate.degreeX
    by_cases hk : k ∈ B.support
    ·
      simpa using
        (Finset.le_sup (s := B.support) (f := fun t : ℕ => (B.coeff t).natDegree) hk)
    ·
      have hk0 : B.coeff k = 0 := (Polynomial.notMem_support_iff.mp hk)
      simp [hk0]

  -- Column-wise `X`-degree bounds for the Sylvester matrix:
  -- first `n` columns come from `A`, last `m` columns come from `B`.
  let colBound : Fin (n + m) → ℕ :=
    Fin.addCases (fun _ : Fin n => Polynomial.Bivariate.degreeX A)
      (fun _ : Fin m => Polynomial.Bivariate.degreeX B)

  have h_entry (σ : Equiv.Perm (Fin (n + m))) (i : Fin (n + m)) :
      (M (σ i) i).natDegree ≤ colBound i := by
    -- split according to whether the column is in the `A`-block or the `B`-block
    cases i using Fin.addCases with
    | left i0 =>
        have hM :
            M (σ (Fin.castAdd m i0)) (Fin.castAdd m i0) =
              (if ((σ (Fin.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m)) then
                  A.coeff ((σ (Fin.castAdd m i0) : ℕ) - i0)
                else 0) := by
          simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
        have hB : colBound (Fin.castAdd m i0) = Polynomial.Bivariate.degreeX A := by
          simp [colBound, Fin.addCases_left]
        simpa [hM, hB] using
          (show (M (σ (Fin.castAdd m i0)) (Fin.castAdd m i0)).natDegree ≤
              colBound (Fin.castAdd m i0) from by
            by_cases h : ((σ (Fin.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
            ·
              simp [hM, hB, h]
              exact hAcoeff ((σ (Fin.castAdd m i0) : ℕ) - i0)
            ·
              simp [hM, hB, h])
    | right i0 =>
        have hM :
            M (σ (Fin.natAdd n i0)) (Fin.natAdd n i0) =
              (if ((σ (Fin.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n)) then
                  B.coeff ((σ (Fin.natAdd n i0) : ℕ) - i0)
                else 0) := by
          simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
        have hB : colBound (Fin.natAdd n i0) = Polynomial.Bivariate.degreeX B := by
          simp [colBound, Fin.addCases_right]
        simpa [hM, hB] using
          (show (M (σ (Fin.natAdd n i0)) (Fin.natAdd n i0)).natDegree ≤
              colBound (Fin.natAdd n i0) from by
            by_cases h : ((σ (Fin.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
            ·
              simp [hM, hB, h]
              exact hBcoeff ((σ (Fin.natAdd n i0) : ℕ) - i0)
            ·
              simp [hM, hB, h])

  have h_term (σ : Equiv.Perm (Fin (n + m))) :
      (Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i).natDegree ≤
        m * Polynomial.Bivariate.degreeX B + n * Polynomial.Bivariate.degreeX A := by
    refine le_trans
      (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) (∏ i : Fin (n + m), M (σ i) i)) ?_
    have hprod :
        (∏ i : Fin (n + m), M (σ i) i).natDegree ≤
          ∑ i : Fin (n + m), (M (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Fin (n + m))))
          (f := fun i : Fin (n + m) => M (σ i) i))
    refine le_trans hprod ?_
    have hsum :
        (∑ i : Fin (n + m), (M (σ i) i).natDegree) ≤ ∑ i : Fin (n + m), colBound i := by
      classical
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n + m))))
          (by
            intro i hi
            exact h_entry σ i))
    refine le_trans hsum ?_
    -- Compute the sum of the column bounds.
    have hcolSum : (∑ i : Fin (n + m), colBound i) =
        n * Polynomial.Bivariate.degreeX A + m * Polynomial.Bivariate.degreeX B := by
      -- `Fin.sum_univ_add` splits the sum over `Fin (n + m)`.
      simpa [colBound, Fin.sum_univ_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Fin.sum_univ_add (f := colBound) (a := n) (b := m))
    -- Reorder the two summands to match the target.
    simpa [hcolSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc]

  have hdet :
      (M.det).natDegree ≤ m * Polynomial.Bivariate.degreeX B + n * Polynomial.Bivariate.degreeX A := by
    classical
    rw [Matrix.det_apply]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := (Finset.univ : Finset (Equiv.Perm (Fin (n + m)))))
      (f := fun σ : Equiv.Perm (Fin (n + m)) =>
        Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i)
      (n := m * Polynomial.Bivariate.degreeX B + n * Polynomial.Bivariate.degreeX A)
      (by
        intro σ hσ
        simpa using h_term σ)

  -- Finish by unfolding `Polynomial.resultant`.
  simpa [Polynomial.resultant, M, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hdet


theorem PS_resultant_map {R S : Type} [CommRing R] [CommRing S]
  (f : R →+* S) (p q : R[X]) (m n : ℕ) :
  f (Polynomial.resultant p q m n) = Polynomial.resultant (p.map f) (q.map f) m n := by
  classical
  -- unfold resultant and push `f` through the determinant
  simp [Polynomial.resultant, RingHom.map_det]
  -- reduce to showing the Sylvester matrices agree entrywise after mapping
  congr 1
  ext i j
  -- split on whether the column index `j` lies in the `p`-block or the `q`-block
  refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
  · -- `j` in the `p`-block
    by_cases h : ((j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + m)
    · simp [Polynomial.sylvester, Matrix.of_apply, RingHom.mapMatrix_apply, Polynomial.coeff_map, h]
    · simp [Polynomial.sylvester, Matrix.of_apply, RingHom.mapMatrix_apply, Polynomial.coeff_map, h]
  · -- `j` in the `q`-block
    by_cases h : ((j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + n)
    · simp [Polynomial.sylvester, Matrix.of_apply, RingHom.mapMatrix_apply, Polynomial.coeff_map, h]
    · simp [Polynomial.sylvester, Matrix.of_apply, RingHom.mapMatrix_apply, Polynomial.coeff_map, h]

theorem PS_resultant_evalX {F : Type} [Field F]
  (x : F) (A B : F[X][Y]) (m n : ℕ) :
  (Polynomial.evalRingHom x) (Polynomial.resultant A B m n) =
    Polynomial.resultant (A.map (Polynomial.evalRingHom x)) (B.map (Polynomial.evalRingHom x))
      m n := by
  simpa using
    (PS_resultant_map (f := Polynomial.evalRingHom x) (p := A) (q := B) (m := m) (n := n))


theorem PS_sylvester_map {R S : Type} [CommRing R] [CommRing S]
  (f : R →+* S) (A B : R[X]) (m n : ℕ) :
  (Polynomial.sylvester A B m n).map f =
    Polynomial.sylvester (A.map f) (B.map f) m n := by
  ext i j
  cases j using Fin.addCases with
  | left j =>
      by_cases h : ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + m)
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
  | right j =>
      by_cases h : ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + n)
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]

theorem PS_sylvester_mulVec_eq_coeff_add {R : Type} [CommRing R]
  (A B : R[X]) (m n : ℕ)
  (hm : A.natDegree ≤ m) (hn : B.natDegree ≤ n)
  (v : Fin (n + m) → R) :
  (Polynomial.sylvester A B m n).mulVec v =
    fun i : Fin (n + m) =>
      (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))) +
        B * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ) := by
  classical
  ext i
  -- expand the Sylvester matrix-vector product into the two block sums
  simp [Polynomial.sylvester, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.of_apply, Set.mem_Icc]
  -- rewrite each block sum as a coefficient of a polynomial product
  · -- first block (A)
    have hA :=
      (PS_coeff_mul_sum_monomial (A := A) (m := m) (n := n) hm
        (c := fun j : Fin n => v (Fin.castAdd m j)) (i := (i : ℕ)))
    have hB :=
      (PS_coeff_mul_sum_monomial (A := B) (m := n) (n := m) hn
        (c := fun j : Fin m => v (Fin.natAdd n j)) (i := (i : ℕ)))
    -- after rewriting, the goal becomes reflexive
    simpa [hA, hB, add_assoc, add_left_comm, add_comm]


theorem PS_resultant_dvd_pow_evalX {F : Type} [Field F] [DecidableEq F]
  (A B : F[X][Y]) (x : F) (Q : F[X]) (n : ℕ)
  (hmn : Polynomial.Bivariate.natDegreeY A ≤ n)
  (hn : Polynomial.Bivariate.natDegreeY B ≤ n)
  (hQdeg : Q.natDegree ≤ n - Polynomial.Bivariate.natDegreeY A)
  (hQ : Polynomial.Bivariate.evalX x B = Q * Polynomial.Bivariate.evalX x A) :
  (X - C x) ^ (Polynomial.Bivariate.natDegreeY A) ∣
    Polynomial.resultant A B (Polynomial.Bivariate.natDegreeY A) n := by
  classical
  -- rename `m` for the Y-degree of `A`
  set m : ℕ := Polynomial.Bivariate.natDegreeY A with hm
  have hmn' : m ≤ n := by
    simpa [hm] using hmn
  have hQdeg' : Q.natDegree ≤ n - m := by
    simpa [hm] using hQdeg

  let p : F[X] := X - C x
  let M0 : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := Polynomial.sylvester A B m n

  -- Column-operation matrix: identity on the left block, and subtract a linear combination of
  -- the left block from each right-block column.
  let U : Matrix (Fin (n + m)) (Fin (n + m)) F[X] :=
    fun i j =>
      j.addCases
        (fun jn => if i = Fin.castAdd m jn then 1 else 0)
        (fun jm =>
          i.addCases
            (fun in_ => -C ((Q * X ^ (jm : ℕ)).coeff in_))
            (fun im_ => if im_ = jm then 1 else 0))

  let M1 : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := M0 * U

  -- `U` is upper triangular with ones on the diagonal, hence has determinant `1`.
  have hUtri : U.BlockTriangular (fun x : Fin (n + m) => x) := by
    intro i j hij
    -- work by cases on whether indices are in the left/right block
    cases' j using Fin.addCases with jn jm
    · -- `j` in the left block
      have hne : i ≠ Fin.castAdd m jn := ne_of_gt hij
      -- unfold `U` on a left-block column
      simp [U, hne]
    · -- `j` in the right block
      cases' i using Fin.addCases with in_ im_
      · -- `i` in the left block: impossible since then `i < j`
        exfalso
        have hlt : (Fin.castAdd m in_ : Fin (n + m)) < Fin.natAdd n jm := by
          -- compare `val`
          apply Fin.lt_iff_val_lt_val.2
          have : (in_ : ℕ) < n + (jm : ℕ) :=
            lt_of_lt_of_le in_.isLt (Nat.le_add_right n (jm : ℕ))
          simpa using this
        exact (not_lt_of_ge hlt.le hij)
      · -- both in the right block
        have hne : im_ ≠ jm := by
          intro hEq
          apply ne_of_gt hij
          simpa [hEq]
        simp [U, hne]

  have hUdet : U.det = 1 := by
    classical
    have hdet := Matrix.det_of_upperTriangular (M := U) hUtri
    have hdiag : (∏ i : Fin (n + m), U i i) = 1 := by
      -- split the diagonal product into the first `n` and last `m` indices
      have hsplit :=
        (Fin.prod_univ_add (a := n) (b := m) (f := fun i : Fin (n + m) => U i i))
      have hleft : (∏ i : Fin n, U (Fin.castAdd m i) (Fin.castAdd m i)) = 1 := by
        simp [U]
      have hright : (∏ i : Fin m, U (Fin.natAdd n i) (Fin.natAdd n i)) = 1 := by
        simp [U]
      simpa [hsplit, hleft, hright, mul_one]
    simpa [hdiag] using hdet

  have hdet1 : M1.det = M0.det := by
    classical
    -- det(M0 * U) = det M0 * det U = det M0
    simp [M1, Matrix.det_mul, hUdet, M0]

  -- show each entry of the right-block columns of `M1` is divisible by `p`
  have hdiv_entry : ∀ (i : Fin (n + m)) (j' : Fin m), p ∣ M1 i (Fin.natAdd n j') := by
    intro i j'
    let ev : F[X] →+* F := Polynomial.evalRingHom x
    let col : Fin (n + m) := Fin.natAdd n j'
    let vcol : Fin (n + m) → F := fun k => ev (U k col)

    -- enough to show the entry evaluates to zero at `x`
    have hx0 : ev (M1 i col) = 0 := by
      -- map the matrix product through `ev`
      have hmapmul : ev (M1 i col) = (M0.map ev * U.map ev) i col := by
        simpa [M1] using
          (RingHom.map_matrix_mul (M := M0) (N := U) (i := i) (j := col) (f := ev))

      have hmulVec : (M0.map ev * U.map ev) i col = (M0.map ev).mulVec vcol i := by
        -- definitional unfolding of `mulVec`/`dotProduct`
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, vcol]

      have hM0map : M0.map ev = Polynomial.sylvester (A.map ev) (B.map ev) m n := by
        simpa [M0] using (PS_sylvester_map (R := F[X]) (S := F) ev A B m n)

      -- rewrite in terms of the Sylvester matrix over `F`
      have hSylv : ev (M1 i col) =
          (Polynomial.sylvester (A.map ev) (B.map ev) m n).mulVec vcol i := by
        calc
          ev (M1 i col) = (M0.map ev * U.map ev) i col := hmapmul
          _ = (M0.map ev).mulVec vcol i := hmulVec
          _ = (Polynomial.sylvester (A.map ev) (B.map ev) m n).mulVec vcol i := by
            simpa [hM0map]

      -- degree hypotheses for applying `PS_sylvester_mulVec_eq_coeff_add`
      have hmA : (A.map ev).natDegree ≤ m := by
        have h1 : (A.map ev).natDegree ≤ A.natDegree := by
          simpa using (Polynomial.natDegree_map_le (f := ev) (p := A))
        have h2 : A.natDegree ≤ m := by
          -- `m = natDegreeY A = A.natDegree`
          simpa [hm, Polynomial.Bivariate.natDegreeY] using (le_rfl : A.natDegree ≤ A.natDegree)
        exact le_trans h1 h2

      have hnB : (B.map ev).natDegree ≤ n := by
        have h1 : (B.map ev).natDegree ≤ B.natDegree := by
          simpa using (Polynomial.natDegree_map_le (f := ev) (p := B))
        have h2 : B.natDegree ≤ n := by
          simpa [Polynomial.Bivariate.natDegreeY] using hn
        exact le_trans h1 h2

      -- compute the `mulVec` entry
      have hmulVecCoeff :=
        congrArg (fun f : (Fin (n + m) → F) => f i)
          (PS_sylvester_mulVec_eq_coeff_add (A := A.map ev) (B := B.map ev) (m := m) (n := n)
            hmA hnB vcol)

      -- simplify the two sums appearing in the formula
      let q : F[X] := Q * X ^ (j' : ℕ)

      have hqdeg_le : q.natDegree ≤ n - 1 := by
        simpa [q] using (PS_natDegree_mul_X_pow_le (Q := Q) (j := j') hmn' hQdeg')

      have hqdeg_lt : q.natDegree < n := by
        have hmpos : 0 < m := Fin.size_positive j'
        have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn'
        have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
        have hlt : n - 1 < n := by
          simpa [hsub] using (Nat.lt_succ_self (n - 1))
        exact lt_of_le_of_lt hqdeg_le hlt

      have hBmap : B.map ev = Q * A.map ev := by
        -- rewrite `evalX` as `map` in the hypothesis `hQ`
        simpa [PS_evalX_eq_map, ev] using hQ

      have hsum_left : (∑ j : Fin n, Polynomial.monomial (j : ℕ) (vcol (Fin.castAdd m j))) = -q := by
        -- identify this sum with `ofFn n` applied to `-toFn n q`
        have hsum1 : (∑ j : Fin n, Polynomial.monomial (j : ℕ) (vcol (Fin.castAdd m j))) =
            Polynomial.ofFn n (fun j : Fin n => vcol (Fin.castAdd m j)) := by
          simpa using
            (Polynomial.ofFn_eq_sum_monomial (v := fun j : Fin n => vcol (Fin.castAdd m j))).symm

        -- compute the coefficient vector
        have hv : (fun j : Fin n => vcol (Fin.castAdd m j)) =
            fun j : Fin n => -(Polynomial.toFn n q j) := by
          funext j
          -- on the left block, `U` has constant entries `-C (q.coeff j)`
          simp [vcol, col, U, ev, q, Polynomial.toFn]

        -- reconstruct `q` from its first `n` coefficients
        have hofFn : Polynomial.ofFn n (Polynomial.toFn n q) = q :=
          Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (p := q) hqdeg_lt

        have hofFn_neg :
            Polynomial.ofFn n (fun j : Fin n => -(Polynomial.toFn n q j)) =
              -Polynomial.ofFn n (Polynomial.toFn n q) := by
          classical
          -- convert to sum of monomials and pull out the minus
          simp [Polynomial.ofFn_eq_sum_monomial, Fintype.sum_neg]

        -- put everything together
        calc
          (∑ j : Fin n, Polynomial.monomial (j : ℕ) (vcol (Fin.castAdd m j)))
              = Polynomial.ofFn n (fun j : Fin n => vcol (Fin.castAdd m j)) := hsum1
          _ = Polynomial.ofFn n (fun j : Fin n => -(Polynomial.toFn n q j)) := by
            simpa [hv]
          _ = -Polynomial.ofFn n (Polynomial.toFn n q) := hofFn_neg
          _ = -q := by
            simpa [hofFn]

      have hsum_right : (∑ j : Fin m, Polynomial.monomial (j : ℕ) (vcol (Fin.natAdd n j))) =
          X ^ (j' : ℕ) := by
        classical
        have hv : ∀ j : Fin m, vcol (Fin.natAdd n j) = (if j = j' then (1 : F) else 0) := by
          intro j
          by_cases h : j = j'
          · simp [vcol, col, U, ev, h]
          · simp [vcol, col, U, ev, h]

        -- convert to a delta-sum
        have hdelta :
            (∑ j : Fin m, Polynomial.monomial (j : ℕ) (if j = j' then (1 : F) else 0)) =
              X ^ (j' : ℕ) := by
          classical
          calc
            (∑ j : Fin m, Polynomial.monomial (j : ℕ) (if j = j' then (1 : F) else 0))
                = ∑ j : Fin m, (if j = j' then Polynomial.monomial (j : ℕ) (1 : F) else 0) := by
                    classical
                    have hfun :
                        (fun j : Fin m => Polynomial.monomial (j : ℕ) (if j = j' then (1 : F) else 0)) =
                          fun j : Fin m => (if j = j' then Polynomial.monomial (j : ℕ) (1 : F) else 0) := by
                      funext j
                      by_cases hj : j = j'
                      · simp [hj]
                      · simp [hj]
                    simpa [hfun]
            _ = Polynomial.monomial (j' : ℕ) (1 : F) := by
                simpa using (Fintype.sum_ite_eq
                  (f := fun j : Fin m => Polynomial.monomial (j : ℕ) (1 : F)) (a := j'))
            _ = X ^ (j' : ℕ) := by
                simpa using (Polynomial.monomial_one_right_eq_X_pow (R := F) (n := (j' : ℕ)))

        simpa [hv] using hdelta

      -- now the coefficient is zero, using `hBmap`
      have hcoeff0 :
          ((A.map ev) * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (vcol (Fin.castAdd m j))) +
            (B.map ev) * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (vcol (Fin.natAdd n j)))).coeff
              (i : ℕ) = 0 := by
        -- rewrite the two sums
        simp [hsum_left, hsum_right, hBmap, q, mul_assoc, mul_left_comm, mul_comm]

      -- finish
      have : (Polynomial.sylvester (A.map ev) (B.map ev) m n).mulVec vcol i = 0 := by
        -- `hmulVecCoeff` is exactly this coefficient
        simpa [hmulVecCoeff, hcoeff0] using congrArg id hmulVecCoeff

      -- use the rewriting of `ev (M1 i col)` via Sylvester
      simpa [hSylv] using this

    -- convert to `IsRoot`, then to divisibility by `X - C x`
    have hroot : Polynomial.IsRoot (M1 i col) x := by
      have : (M1 i col).eval x = 0 := by
        simpa [ev, Polynomial.coe_evalRingHom] using hx0
      simpa [Polynomial.IsRoot, Polynomial.IsRoot.def] using this

    have hdiv : (X - C x) ∣ M1 i col := (Polynomial.dvd_iff_isRoot).2 hroot
    simpa [p, col] using hdiv

  -- build a matrix by dividing the right-block columns by `p`
  classical
  let Qmat : Matrix (Fin (n + m)) (Fin (n + m)) F[X] :=
    fun i j =>
      j.addCases
        (fun jn => M1 i (Fin.castAdd m jn))
        (fun jm => Classical.choose (hdiv_entry i jm))

  have hQmat_spec : ∀ (i : Fin (n + m)) (j' : Fin m),
      M1 i (Fin.natAdd n j') = p * Qmat i (Fin.natAdd n j') := by
    intro i j'
    simpa [Qmat, Fin.addCases_right] using (Classical.choose_spec (hdiv_entry i j'))

  -- express `M1` as column-scaled version of `Qmat`
  let v : Fin (n + m) → F[X] := fun j => j.addCases (fun _ => 1) (fun _ => p)

  have hM1_scale : M1 = fun i j => v j * Qmat i j := by
    apply Matrix.ext
    intro i j
    cases' j using Fin.addCases with jn jm
    · -- left block
      simp [v, Qmat, Fin.addCases_left]
    · -- right block
      have h := hQmat_spec i jm
      simpa [v, Qmat, Fin.addCases_right, mul_assoc] using h

  have hdet_factor : M1.det = (∏ j : Fin (n + m), v j) * Qmat.det := by
    classical
    simpa [hM1_scale] using (Matrix.det_mul_row v Qmat)

  -- compute product of `v`
  have hvprod : (∏ j : Fin (n + m), v j) = p ^ m := by
    classical
    have hsplit := (Fin.prod_univ_add (a := n) (b := m) (f := v))
    have hleft : (∏ i : Fin n, v (Fin.castAdd m i)) = 1 := by
      simp [v]
    have hright : (∏ j' : Fin m, v (Fin.natAdd n j')) = p ^ m := by
      simp [v]
    simpa [hsplit, hleft, hright]

  -- conclude divisibility for `M1.det`
  have hdivM1 : p ^ m ∣ M1.det := by
    refine ⟨Qmat.det, ?_⟩
    simp [hdet_factor, hvprod, mul_assoc]

  -- transfer back to `M0.det`
  have hdivM0 : p ^ m ∣ M0.det := by
    simpa [hdet1] using hdivM1

  -- rewrite goal
  -- `Polynomial.resultant` is defined as the determinant of the Sylvester matrix
  simpa [p, m, hm, Polynomial.Bivariate.natDegreeY, Polynomial.resultant, M0] using hdivM0

theorem PS_resultant_dvd_pow_evalY {F : Type} [Field F] [DecidableEq F]
  (A B : F[X][Y]) (y : F) (Q : F[X]) (n : ℕ)
  (hmn : Polynomial.Bivariate.degreeX A ≤ n)
  (hn : Polynomial.Bivariate.degreeX B ≤ n)
  (hQdeg : Q.natDegree ≤ n - Polynomial.Bivariate.degreeX A)
  (hQ : Polynomial.Bivariate.evalY y B = Q * Polynomial.Bivariate.evalY y A) :
  (X - C y) ^ (Polynomial.Bivariate.degreeX A) ∣
    Polynomial.resultant (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B)
      (Polynomial.Bivariate.degreeX A) n := by
  classical
  have hQ' :
      Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap B) =
        Q * Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap A) := by
    simpa [-Polynomial.Bivariate.swap_apply, PS_evalY_eq_evalX_swap] using hQ

  have hmn' : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) ≤ n := by
    simpa [-Polynomial.Bivariate.swap_apply, PS_natDegreeY_swap] using hmn

  have hn' : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap B) ≤ n := by
    simpa [-Polynomial.Bivariate.swap_apply, PS_natDegreeY_swap] using hn

  have hQdeg' : Q.natDegree ≤ n - Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) := by
    simpa [-Polynomial.Bivariate.swap_apply, PS_natDegreeY_swap] using hQdeg

  have h :=
    PS_resultant_dvd_pow_evalX (A := Polynomial.Bivariate.swap A)
      (B := Polynomial.Bivariate.swap B) (x := y) (Q := Q) (n := n)
      (hmn := hmn') (hn := hn') (hQdeg := hQdeg') (hQ := hQ')

  simpa [-Polynomial.Bivariate.swap_apply, PS_natDegreeY_swap] using h


theorem PS_resultant_ne_zero_of_isRelPrime {F : Type} [Field F] [DecidableEq F]
  (A B : F[X][Y]) (n : ℕ)
  (hn : Polynomial.Bivariate.natDegreeY B ≤ n)
  (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hrel : IsRelPrime A B) :
  Polynomial.resultant A B (Polynomial.Bivariate.natDegreeY A) n ≠ 0 := by
  classical
  set m : ℕ := Polynomial.Bivariate.natDegreeY A with hm
  clear_value m
  intro hres
  have hdet : (Polynomial.sylvester A B m n).det = 0 := by
    simpa [Polynomial.resultant] using hres
  rcases (Matrix.exists_mulVec_eq_zero_iff (M := Polynomial.sylvester A B m n)).2 hdet with
    ⟨v, hv0, hv⟩
  have hmdeg : A.natDegree ≤ m := by
    simpa [hm, Polynomial.Bivariate.natDegreeY] using (le_rfl : A.natDegree ≤ A.natDegree)
  have hndeg : B.natDegree ≤ n := by
    simpa [Polynomial.Bivariate.natDegreeY] using hn
  let P : F[X][Y] :=
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))
  let Q : F[X][Y] :=
    ∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j))
  have hvcoeff : ∀ i : Fin (n + m), (A * P + B * Q).coeff (i : ℕ) = 0 := by
    intro i
    have hv_i : (Polynomial.sylvester A B m n).mulVec v i = 0 := by
      simpa using congrArg (fun f => f i) hv
    have hsyl_i :=
      congrArg (fun f => f i)
        (PS_sylvester_mulVec_eq_coeff_add (R := F[X]) A B m n hmdeg hndeg v)
    have :
        (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))) +
            B * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ) = 0 := by
      calc
        (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))) +
              B * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ)
            = (Polynomial.sylvester A B m n).mulVec v i := by
                simpa using hsyl_i.symm
        _ = 0 := hv_i
    simpa [P, Q] using this

  -- If `n + m = 0`, then `Fin (n + m)` is empty, so `v = 0`, contradicting `hv0`.
  have hnmpos : 0 < n + m := by
    by_contra h
    have hnm0 : n + m = 0 := Nat.eq_zero_of_not_pos h
    have : v = 0 := by
      funext i
      have hlt : (i : ℕ) < 0 := by
        simpa [hnm0] using i.isLt
      exact (False.elim (Nat.not_lt_zero _ hlt))
    exact hv0 this

  have hA_natDegree : A.natDegree = m := by
    simpa [Polynomial.Bivariate.natDegreeY] using hm.symm

  have hP_ofFn : P = Polynomial.ofFn n (fun j : Fin n => v (Fin.castAdd m j)) := by
    simpa [P] using
      (Polynomial.ofFn_eq_sum_monomial (v := fun j : Fin n => v (Fin.castAdd m j))).symm

  have hQ_ofFn : Q = Polynomial.ofFn m (fun j : Fin m => v (Fin.natAdd n j)) := by
    simpa [Q] using
      (Polynomial.ofFn_eq_sum_monomial (v := fun j : Fin m => v (Fin.natAdd n j))).symm

  have hdegC : (A * P + B * Q).natDegree < n + m := by
    have hdegAP : (A * P).natDegree < n + m := by
      by_cases hn0 : n = 0
      · subst hn0
        have hmpos : 0 < m := by simpa using hnmpos
        simpa [P] using hmpos
      · have hnpos : 1 ≤ n := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hn0)
        have hPnat : P.natDegree < n := by
          simpa [hP_ofFn] using
            (Polynomial.ofFn_natDegree_lt (R := F[X]) hnpos (fun j : Fin n => v (Fin.castAdd m j)))
        have hmul_le : (A * P).natDegree ≤ A.natDegree + P.natDegree := Polynomial.natDegree_mul_le
        have hmul_le' : (A * P).natDegree ≤ m + P.natDegree := by
          simpa [hA_natDegree] using hmul_le
        have hlt : m + P.natDegree < m + n := Nat.add_lt_add_left hPnat m
        have : (A * P).natDegree < m + n := lt_of_le_of_lt hmul_le' hlt
        simpa [Nat.add_comm] using this

    have hdegBQ : (B * Q).natDegree < n + m := by
      by_cases hm0 : m = 0
      · subst hm0
        have hnpos : 0 < n := by simpa using hnmpos
        simpa [Q] using hnpos
      · have hmpos : 1 ≤ m := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hm0)
        have hQnat : Q.natDegree < m := by
          simpa [hQ_ofFn] using
            (Polynomial.ofFn_natDegree_lt (R := F[X]) hmpos (fun j : Fin m => v (Fin.natAdd n j)))
        have hmul_le : (B * Q).natDegree ≤ B.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
        have h1 : B.natDegree + Q.natDegree ≤ n + Q.natDegree := Nat.add_le_add_right hndeg _
        have h2 : n + Q.natDegree < n + m := Nat.add_lt_add_left hQnat n
        exact lt_of_le_of_lt hmul_le (lt_of_le_of_lt h1 h2)

    have hle : (A * P + B * Q).natDegree ≤ max (A * P).natDegree (B * Q).natDegree :=
      Polynomial.natDegree_add_le (A * P) (B * Q)
    have hmaxlt : max (A * P).natDegree (B * Q).natDegree < n + m :=
      max_lt_iff.2 ⟨hdegAP, hdegBQ⟩
    exact lt_of_le_of_lt hle hmaxlt

  have hcomb : A * P + B * Q = 0 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < n + m
    · simpa using hvcoeff ⟨k, hk⟩
    · have hk' : n + m ≤ k := Nat.le_of_not_gt hk
      have hdegk : (A * P + B * Q).natDegree < k := lt_of_lt_of_le hdegC hk'
      simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt hdegk)

  have hA_dvd_BQ : A ∣ B * Q := by
    refine ⟨-P, ?_⟩
    have hcomb' : B * Q + A * P = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hcomb
    have hneg : -(A * P) = B * Q := neg_eq_of_add_eq_zero_left hcomb'
    calc
      B * Q = -(A * P) := by simpa using hneg.symm
      _ = A * (-P) := (mul_neg A P).symm

  have hA_dvd_Q : A ∣ Q := hrel.dvd_of_dvd_mul_left hA_dvd_BQ

  have hQ0 : Q = 0 := by
    by_cases hm0 : m = 0
    · subst hm0
      simp [Q]
    · have hmpos : 1 ≤ m := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hm0)
      have hQnat : Q.natDegree < m := by
        simpa [hQ_ofFn] using
          (Polynomial.ofFn_natDegree_lt (R := F[X]) hmpos (fun j : Fin m => v (Fin.natAdd n j)))
      rcases hA_dvd_Q with ⟨R, hR⟩
      by_cases hR0 : R = 0
      · subst hR0
        simpa [hR]
      · have hQnat' : (A * R).natDegree < m := by
          simpa [hR] using hQnat
        have hdegmul : (A * R).natDegree = A.natDegree + R.natDegree :=
          Polynomial.natDegree_mul hA0 hR0
        have hlt : A.natDegree + R.natDegree < m := by
          simpa [hdegmul] using hQnat'
        have hlt' : m + R.natDegree < m := by
          simpa [hA_natDegree] using hlt
        have hge : m ≤ m + R.natDegree := Nat.le_add_right m R.natDegree
        exact (False.elim ((Nat.not_lt_of_ge hge) hlt'))

  have hP0 : P = 0 := by
    have hAP0 : A * P = 0 := by
      simpa [hQ0] using hcomb
    have hmul : A = 0 ∨ P = 0 := mul_eq_zero.mp hAP0
    exact hmul.resolve_left hA0

  have hcoeffP : ∀ j : Fin n, P.coeff (j : ℕ) = v (Fin.castAdd m j) := by
    intro j
    simpa [hP_ofFn] using
      (Polynomial.ofFn_coeff_eq_val_of_lt
        (v := fun k : Fin n => v (Fin.castAdd m k)) (hi := j.isLt))

  have hcoeffQ : ∀ j : Fin m, Q.coeff (j : ℕ) = v (Fin.natAdd n j) := by
    intro j
    simpa [hQ_ofFn] using
      (Polynomial.ofFn_coeff_eq_val_of_lt
        (v := fun k : Fin m => v (Fin.natAdd n k)) (hi := j.isLt))

  have hv_left : ∀ j : Fin n, v (Fin.castAdd m j) = 0 := by
    intro j
    have : P.coeff (j : ℕ) = 0 := by
      simpa [hP0]
    simpa [hcoeffP j] using this

  have hv_right : ∀ j : Fin m, v (Fin.natAdd n j) = 0 := by
    intro j
    have : Q.coeff (j : ℕ) = 0 := by
      simpa [hQ0]
    simpa [hcoeffQ j] using this

  have hv_all : ∀ i : Fin (n + m), v i = 0 := by
    exact
      (Fin.forall_fin_add (m := n) (n := m) (P := fun i : Fin (n + m) => v i = 0)).2
        ⟨hv_left, hv_right⟩

  have : v = 0 := by
    funext i
    exact hv_all i

  exact hv0 this

theorem PS_coprime_case_constant {F : Type} [Field F] [DecidableEq F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (A B : F[X][Y])
  (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hrel : IsRelPrime A B)
  (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A)
  (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
  (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A)
  (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧
      Polynomial.Bivariate.evalY y B = (quot_X y) * (Polynomial.Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧
      Polynomial.Bivariate.evalX x B = (quot_Y x) * (Polynomial.Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
  Polynomial.Bivariate.degreeX A = 0 ∧ Polynomial.Bivariate.natDegreeY A = 0 := by
  classical
  -- abbreviations for degrees
  set mY : ℕ := Polynomial.Bivariate.natDegreeY A with hmY
  set mX : ℕ := Polynomial.Bivariate.degreeX A with hmX
  -- resultant in the Y-direction
  set RY : F[X] := Polynomial.resultant A B mY b_y with hRY
  -- for the X-direction we use the swapped polynomials
  set RX : F[X] :=
      Polynomial.resultant (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) mX b_x with hRX

  -- convenient bounds coming from the new hypotheses
  have hmY_le_ay : mY ≤ a_y := by
    simpa [hmY.symm] using h_f_degY
  have hmX_le_ax : mX ≤ a_x := by
    simpa [hmX.symm] using h_f_degX
  have hax_le_bx : a_x ≤ b_x := by
    simpa using h_bx_ge_ax
  have hay_le_by : a_y ≤ b_y := by
    simpa using h_by_ge_ay
  have hmY_le_by : mY ≤ b_y := le_trans hmY_le_ay hay_le_by
  have hmX_le_bx : mX ≤ b_x := le_trans hmX_le_ax hax_le_bx

  -- nonvanishing of the two resultants from coprimality
  have hRY0 : RY ≠ 0 := by
    have h :=
      PS_resultant_ne_zero_of_isRelPrime (A := A) (B := B) (n := b_y) (hn := by
        -- natDegreeY B ≤ b_y
        simpa using h_g_degY)
        (hA0 := hA0) (hB0 := hB0) (hrel := hrel)
    simpa [RY, hRY, mY, hmY] using h

  have hA0' : Polynomial.Bivariate.swap A ≠ 0 := by
    intro h
    apply hA0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simpa using h)

  have hB0' : Polynomial.Bivariate.swap B ≠ 0 := by
    intro h
    apply hB0
    exact (Polynomial.Bivariate.swap (R := F)).injective (by simpa using h)

  have hrel' : IsRelPrime (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) :=
    PS_isRelPrime_swap (A := A) (B := B) hrel

  have hnX : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap B) ≤ b_x := by
    rw [PS_natDegreeY_swap (f := B)]
    simpa using h_g_degX

  have hRX0 : RX ≠ 0 := by
    have h :=
      PS_resultant_ne_zero_of_isRelPrime
        (A := Polynomial.Bivariate.swap A) (B := Polynomial.Bivariate.swap B) (n := b_x) (hn := hnX)
        (hA0 := hA0') (hB0 := hB0') (hrel := hrel')
    -- unfold RX and rewrite the exponent to match the lemma
    rw [hRX]
    have hnat : mX = Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) := by
      -- mX = degreeX A = natDegreeY (swap A)
      exact hmX.trans (PS_natDegreeY_swap (f := A)).symm
    -- replace mX by natDegreeY (swap A)
    rw [hnat]
    simpa using h

  -- divisibility of RY by the product over x∈P_x of (X - C x)^mY
  have hprod_dvd_RY : (∏ x ∈ P_x, (X - C x) ^ mY) ∣ RY := by
    have hpair_all : Pairwise (fun x y : F => IsCoprime (X - C x : F[X]) (X - C y : F[X])) := by
      simpa using
        (Polynomial.pairwise_coprime_X_sub_C (K := F) (s := fun x : F => x)
          (by
            intro a b h
            exact h))
    have hpair : (P_x : Set F).Pairwise
        (fun x y : F => IsCoprime ((X - C x : F[X]) ^ mY) ((X - C y : F[X]) ^ mY)) := by
      intro x hx y hy hxy
      have hcop : IsCoprime (X - C x : F[X]) (X - C y : F[X]) := hpair_all hxy
      simpa using (hcop.pow (m := mY) (n := mY))
    have hdiv : ∀ x ∈ P_x, (X - C x) ^ mY ∣ RY := by
      intro x hx
      rcases h_quot_Y x hx with ⟨hdegQ, hQ⟩
      have h :=
        PS_resultant_dvd_pow_evalX (A := A) (B := B) (x := x) (Q := quot_Y x) (n := b_y)
          (hmn := by
            -- natDegreeY A ≤ b_y
            simpa [hmY.symm] using hmY_le_by)
          (hn := by
            simpa using h_g_degY)
          (hQdeg := by
            have h1 : (quot_Y x).natDegree ≤ b_y - a_y := hdegQ
            have h2 : b_y - a_y ≤ b_y - mY := by
              exact Nat.sub_le_sub_left hmY_le_ay b_y
            exact le_trans h1 h2)
          (hQ := hQ)
      simpa [RY, hRY, mY, hmY] using h
    exact
      Finset.prod_dvd_of_coprime (t := P_x) (s := fun x : F => (X - C x : F[X]) ^ mY) (z := RY)
        hpair hdiv

  -- analogous divisibility for RX over y∈P_y
  have hprod_dvd_RX : (∏ y ∈ P_y, (X - C y) ^ mX) ∣ RX := by
    have hpair_all : Pairwise (fun y y' : F => IsCoprime (X - C y : F[X]) (X - C y' : F[X])) := by
      simpa using
        (Polynomial.pairwise_coprime_X_sub_C (K := F) (s := fun y : F => y)
          (by
            intro a b h
            exact h))
    have hpair : (P_y : Set F).Pairwise
        (fun y y' : F => IsCoprime ((X - C y : F[X]) ^ mX) ((X - C y' : F[X]) ^ mX)) := by
      intro y hy y' hy' hyy'
      have hcop : IsCoprime (X - C y : F[X]) (X - C y' : F[X]) := hpair_all hyy'
      simpa using (hcop.pow (m := mX) (n := mX))
    have hdiv : ∀ y ∈ P_y, (X - C y) ^ mX ∣ RX := by
      intro y hy
      rcases h_quot_X y hy with ⟨hdegQ, hQ⟩
      have h :=
        PS_resultant_dvd_pow_evalY (A := A) (B := B) (y := y) (Q := quot_X y) (n := b_x)
          (hmn := by
            -- degreeX A ≤ b_x
            simpa [hmX.symm] using hmX_le_bx)
          (hn := by
            simpa using h_g_degX)
          (hQdeg := by
            have h1 : (quot_X y).natDegree ≤ b_x - a_x := hdegQ
            have h2 : b_x - a_x ≤ b_x - mX := by
              exact Nat.sub_le_sub_left hmX_le_ax b_x
            exact le_trans h1 h2)
          (hQ := hQ)
      have h' : (X - C y) ^ mX ∣
          Polynomial.resultant (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) mX b_x := by
        simpa [mX, hmX] using h
      simpa [RX, hRX] using h'
    exact
      Finset.prod_dvd_of_coprime (t := P_y) (s := fun y : F => (X - C y : F[X]) ^ mX) (z := RX)
        hpair hdiv

  -- lower bounds on natDegrees from divisibility
  have hdeg_prod_RY : (∏ x ∈ P_x, (X - C x) ^ mY).natDegree = mY * P_x.card := by
    have hne : ∀ x ∈ P_x, (X - C x : F[X]) ^ mY ≠ 0 := by
      intro x hx
      exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
    calc
      (∏ x ∈ P_x, (X - C x : F[X]) ^ mY).natDegree
          = ∑ x ∈ P_x, ((X - C x : F[X]) ^ mY).natDegree := by
              simpa using
                (Polynomial.natDegree_prod (s := P_x) (f := fun x : F => (X - C x : F[X]) ^ mY) hne)
      _ = ∑ x ∈ P_x, mY := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have := (Polynomial.natDegree_pow (p := (X - C x : F[X])) (n := mY))
            simpa [Polynomial.natDegree_X_sub_C, Nat.mul_one] using this
      _ = mY * P_x.card := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  have hdeg_prod_RX : (∏ y ∈ P_y, (X - C y) ^ mX).natDegree = mX * P_y.card := by
    have hne : ∀ y ∈ P_y, (X - C y : F[X]) ^ mX ≠ 0 := by
      intro y hy
      exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero y)
    calc
      (∏ y ∈ P_y, (X - C y : F[X]) ^ mX).natDegree
          = ∑ y ∈ P_y, ((X - C y : F[X]) ^ mX).natDegree := by
              simpa using
                (Polynomial.natDegree_prod (s := P_y) (f := fun y : F => (X - C y : F[X]) ^ mX) hne)
      _ = ∑ y ∈ P_y, mX := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            have := (Polynomial.natDegree_pow (p := (X - C y : F[X])) (n := mX))
            simpa [Polynomial.natDegree_X_sub_C, Nat.mul_one] using this
      _ = mX * P_y.card := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  have hmy_card_le : mY * (n_x : ℕ) ≤ RY.natDegree := by
    have h1 : (∏ x ∈ P_x, (X - C x) ^ mY).natDegree ≤ RY.natDegree :=
      Polynomial.natDegree_le_of_dvd hprod_dvd_RY hRY0
    have hnx : (n_x : ℕ) ≤ P_x.card := h_card_Px
    have h2 : mY * (n_x : ℕ) ≤ mY * P_x.card := Nat.mul_le_mul_left _ hnx
    calc
      mY * (n_x : ℕ) ≤ mY * P_x.card := h2
      _ = (∏ x ∈ P_x, (X - C x) ^ mY).natDegree := by
            simpa [hdeg_prod_RY]
      _ ≤ RY.natDegree := h1

  have hmx_card_le : mX * (n_y : ℕ) ≤ RX.natDegree := by
    have h1 : (∏ y ∈ P_y, (X - C y) ^ mX).natDegree ≤ RX.natDegree :=
      Polynomial.natDegree_le_of_dvd hprod_dvd_RX hRX0
    have hny : (n_y : ℕ) ≤ P_y.card := h_card_Py
    have h2 : mX * (n_y : ℕ) ≤ mX * P_y.card := Nat.mul_le_mul_left _ hny
    calc
      mX * (n_y : ℕ) ≤ mX * P_y.card := h2
      _ = (∏ y ∈ P_y, (X - C y) ^ mX).natDegree := by
            simpa [hdeg_prod_RX]
      _ ≤ RX.natDegree := h1

  -- upper bounds on natDegrees from the given resultant degree lemma
  have hRY_le : RY.natDegree ≤ mY * b_x + mX * b_y := by
    have hdeg :=
      PS_natDegree_resultant_le (A := A) (B := B) (m := mY) (n := b_y)
        (hm := by
          simpa [mY, hmY])
        (hn := by simpa using h_g_degY)
    have hdeg' :
        RY.natDegree ≤ mY * Polynomial.Bivariate.degreeX B + b_y * Polynomial.Bivariate.degreeX A := by
      simpa [RY, hRY] using hdeg
    have hBx : Polynomial.Bivariate.degreeX B ≤ b_x := by
      simpa using h_g_degX
    have h1 : mY * Polynomial.Bivariate.degreeX B ≤ mY * b_x := Nat.mul_le_mul_left _ hBx
    have h2 : b_y * Polynomial.Bivariate.degreeX A ≤ mX * b_y := by
      -- rewrite degreeX A as mX
      have : b_y * Polynomial.Bivariate.degreeX A = mX * b_y := by
        -- commutativity of Nat multiplication
        simpa [mX, hmX, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (by ac_rfl : b_y * Polynomial.Bivariate.degreeX A = mX * b_y)
      exact le_of_eq this
    have hsum :
        mY * Polynomial.Bivariate.degreeX B + b_y * Polynomial.Bivariate.degreeX A ≤ mY * b_x + mX * b_y :=
      Nat.add_le_add h1 h2
    exact le_trans hdeg' hsum

  have hRX_le : RX.natDegree ≤ mX * b_y + mY * b_x := by
    have hm_swap : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) ≤ mX := by
      simpa [hmX.symm] using (le_of_eq (PS_natDegreeY_swap (f := A)))
    have hdeg :=
      PS_natDegree_resultant_le (A := Polynomial.Bivariate.swap A) (B := Polynomial.Bivariate.swap B)
        (m := mX) (n := b_x)
        (hm := hm_swap)
        (hn := hnX)
    have hdeg' :
        RX.natDegree ≤
          mX * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap B) +
            b_x * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap A) := by
      simpa [RX, hRX] using hdeg
    have h1 : mX * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap B) ≤ mX * b_y := by
      -- degreeX (swap B) = natDegreeY B ≤ b_y
      rw [PS_degreeX_swap (f := B)]
      have : Polynomial.Bivariate.natDegreeY B ≤ b_y := by
        simpa using h_g_degY
      exact Nat.mul_le_mul_left _ this
    have h2 : b_x * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap A) ≤ mY * b_x := by
      -- degreeX (swap A) = natDegreeY A = mY
      rw [PS_degreeX_swap (f := A)]
      -- now both sides are equal by commutativity
      have : b_x * Polynomial.Bivariate.natDegreeY A = mY * b_x := by
        -- rewrite natDegreeY A as mY
        simpa [hmY.symm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (by ac_rfl : b_x * Polynomial.Bivariate.natDegreeY A = mY * b_x)
      exact le_of_eq this
    have hsum :
        mX * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap B) +
            b_x * Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap A)
          ≤ mX * b_y + mY * b_x :=
      Nat.add_le_add h1 h2
    exact le_trans hdeg' hsum

  -- combine bounds to get the key inequalities
  have hmy_le_D : mY * (n_x : ℕ) ≤ mX * b_y + mY * b_x := by
    -- align terms using commutativity
    have hRY_le' : RY.natDegree ≤ mX * b_y + mY * b_x := by
      have : mY * b_x + mX * b_y = mX * b_y + mY * b_x := by ac_rfl
      exact le_trans hRY_le (by simpa [this] using le_rfl)
    exact le_trans hmy_card_le hRY_le'

  have hmx_le_D : mX * (n_y : ℕ) ≤ mX * b_y + mY * b_x := by
    exact le_trans hmx_card_le hRX_le

  -- Now use the rational inequality to show the common bound must be 0.
  have hD0 : mX * b_y + mY * b_x = 0 := by
    have hn_x0 : (0 : ℚ) < (n_x : ℚ) := by
      exact_mod_cast (show (0 : ℕ) < (n_x : ℕ) from n_x.pos)
    have hn_y0 : (0 : ℚ) < (n_y : ℚ) := by
      exact_mod_cast (show (0 : ℕ) < (n_y : ℕ) from n_y.pos)
    -- cast the inequalities
    have hmyq : (mY : ℚ) * (n_x : ℚ) ≤ ((mX * b_y + mY * b_x : ℕ) : ℚ) := by
      exact_mod_cast hmy_le_D
    have hmxq : (mX : ℚ) * (n_y : ℚ) ≤ ((mX * b_y + mY * b_x : ℕ) : ℚ) := by
      exact_mod_cast hmx_le_D
    set D : ℚ := ((mX * b_y + mY * b_x : ℕ) : ℚ) with hD
    have hD_nonneg : 0 ≤ D := by
      simpa [D] using (Nat.cast_nonneg (mX * b_y + mY * b_x : ℕ))
    have hn_x0' : (n_x : ℚ) ≠ 0 := ne_of_gt hn_x0
    have hn_y0' : (n_y : ℚ) ≠ 0 := ne_of_gt hn_y0
    have h1 : (mY : ℚ) * (b_x : ℚ) ≤ D * ((b_x : ℚ) / (n_x : ℚ)) := by
      have hb : (mY : ℚ) * (n_x : ℚ) ≤ D := by
        simpa [D] using hmyq
      have hnonneg : 0 ≤ (b_x : ℚ) / (n_x : ℚ) := by
        exact div_nonneg (by exact_mod_cast (Nat.zero_le b_x)) (le_of_lt hn_x0)
      have hb' := mul_le_mul_of_nonneg_right hb hnonneg
      have : (mY : ℚ) * (n_x : ℚ) * ((b_x : ℚ) / (n_x : ℚ)) = (mY : ℚ) * (b_x : ℚ) := by
        field_simp [hn_x0']
        ring
      simpa [mul_assoc, this] using hb'
    have h2 : (mX : ℚ) * (b_y : ℚ) ≤ D * ((b_y : ℚ) / (n_y : ℚ)) := by
      have hb : (mX : ℚ) * (n_y : ℚ) ≤ D := by
        simpa [D] using hmxq
      have hnonneg : 0 ≤ (b_y : ℚ) / (n_y : ℚ) := by
        exact div_nonneg (by exact_mod_cast (Nat.zero_le b_y)) (le_of_lt hn_y0)
      have hb' := mul_le_mul_of_nonneg_right hb hnonneg
      have : (mX : ℚ) * (n_y : ℚ) * ((b_y : ℚ) / (n_y : ℚ)) = (mX : ℚ) * (b_y : ℚ) := by
        field_simp [hn_y0']
        ring
      simpa [mul_assoc, this] using hb'
    have hDexpr : D = (mX : ℚ) * (b_y : ℚ) + (mY : ℚ) * (b_x : ℚ) := by
      simp [D, Nat.cast_add, Nat.cast_mul, mul_add, add_mul]
    have hDle : D ≤ D * ((b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) := by
      have : (mX : ℚ) * (b_y : ℚ) + (mY : ℚ) * (b_x : ℚ) ≤
          D * ((b_y : ℚ) / (n_y : ℚ)) + D * ((b_x : ℚ) / (n_x : ℚ)) := by
        exact add_le_add h2 h1
      have : D ≤ D * ((b_y : ℚ) / (n_y : ℚ)) + D * ((b_x : ℚ) / (n_x : ℚ)) := by
        simpa [hDexpr] using this
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using this
    have hlt : (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) < 1 := by
      linarith
    have : D = 0 := by
      by_contra hD0
      have hDpos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
      have hmul_lt : D * ((b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) < D := by
        have := mul_lt_mul_of_pos_left hlt hDpos
        simpa [mul_one] using this
      have := lt_of_le_of_lt hDle hmul_lt
      exact lt_irrefl _ this
    have : ((mX * b_y + mY * b_x : ℕ) : ℚ) = 0 := by
      simpa [D] using this
    exact (Nat.cast_inj (R := ℚ)).1 (by simpa using this)

  -- finally deduce mX = 0 and mY = 0 from the inequalities with n_x,n_y > 0
  have hmX0 : mX = 0 := by
    have hle : mX * (n_y : ℕ) ≤ 0 := by
      simpa [hD0] using hmx_le_D
    have hmul : mX * (n_y : ℕ) = 0 := Nat.eq_zero_of_le_zero hle
    have hny0 : (n_y : ℕ) ≠ 0 := Nat.ne_of_gt n_y.pos
    have : mX = 0 ∨ (n_y : ℕ) = 0 := by
      simpa using (mul_eq_zero.mp hmul)
    exact this.resolve_right hny0

  have hmY0 : mY = 0 := by
    have hle : mY * (n_x : ℕ) ≤ 0 := by
      simpa [hD0] using hmy_le_D
    have hmul : mY * (n_x : ℕ) = 0 := Nat.eq_zero_of_le_zero hle
    have hnx0 : (n_x : ℕ) ≠ 0 := Nat.ne_of_gt n_x.pos
    have : mY = 0 ∨ (n_x : ℕ) = 0 := by
      simpa using (mul_eq_zero.mp hmul)
    exact this.resolve_right hnx0

  refine ⟨?_, ?_⟩
  · simpa [mX, hmX] using hmX0
  · simpa [mY, hmY] using hmY0


theorem PS_exists_P_nonzero {F : Type} [Field F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (A B : F[X][Y])
  (hA0 : A ≠ 0) (hB0 : B ≠ 0)
  (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A) (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
  (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A) (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧
      Polynomial.Bivariate.evalY y B = (quot_X y) * (Polynomial.Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧
      Polynomial.Bivariate.evalX x B = (quot_Y x) * (Polynomial.Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  : ∃ P : F[X][Y], B = P * A := by
  classical
  rcases PS_gcd_decompose (A := A) (B := B) hA0 hB0 with ⟨G, A1, B1, hA, hB, hrel, hA1, hB1⟩
  have hG0 : G ≠ 0 := by
    intro hG
    apply hA0
    simpa [hA, hG] using hA
  -- degrees of the gcd factor
  set gx : ℕ := Polynomial.Bivariate.degreeX G
  set gy : ℕ := Polynomial.Bivariate.natDegreeY G
  have hdegX_A : Polynomial.Bivariate.degreeX A = gx + Polynomial.Bivariate.degreeX A1 := by
    rw [hA]
    simpa [gx] using
      (Polynomial.Bivariate.degreeX_mul (F := F) (f := G) (g := A1) hG0 hA1)
  have hdegY_A : Polynomial.Bivariate.natDegreeY A = gy + Polynomial.Bivariate.natDegreeY A1 := by
    rw [hA]
    simpa [gy] using
      (Polynomial.Bivariate.degreeY_mul (F := F) (f := G) (g := A1) hG0 hA1)
  have hdegX_B : Polynomial.Bivariate.degreeX B = gx + Polynomial.Bivariate.degreeX B1 := by
    rw [hB]
    simpa [gx] using
      (Polynomial.Bivariate.degreeX_mul (F := F) (f := G) (g := B1) hG0 hB1)
  have hdegY_B : Polynomial.Bivariate.natDegreeY B = gy + Polynomial.Bivariate.natDegreeY B1 := by
    rw [hB]
    simpa [gy] using
      (Polynomial.Bivariate.degreeY_mul (F := F) (f := G) (g := B1) hG0 hB1)
  -- inequalities gx < n_x and gy < n_y
  have hbxltnx : b_x < (n_x : ℕ) :=
    PS_bx_lt_nx (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
  have hbyltny : b_y < (n_y : ℕ) :=
    PS_by_lt_ny (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
  have hgx_le_degA : gx ≤ Polynomial.Bivariate.degreeX A := by
    simpa [hdegX_A] using (Nat.le_add_right gx (Polynomial.Bivariate.degreeX A1))
  have hgy_le_degYA : gy ≤ Polynomial.Bivariate.natDegreeY A := by
    simpa [hdegY_A] using (Nat.le_add_right gy (Polynomial.Bivariate.natDegreeY A1))
  have hgx_le_ax : gx ≤ a_x := le_trans hgx_le_degA h_f_degX
  have hgy_le_ay : gy ≤ a_y := le_trans hgy_le_degYA h_f_degY
  have hgx_le_bx : gx ≤ b_x := le_trans hgx_le_ax h_bx_ge_ax
  have hgy_le_by : gy ≤ b_y := le_trans hgy_le_ay h_by_ge_ay
  have hx_lt_nx : gx < (n_x : ℕ) := lt_of_le_of_lt hgx_le_bx hbxltnx
  have hy_lt_ny : gy < (n_y : ℕ) := lt_of_le_of_lt hgy_le_by hbyltny
  -- filtered sets
  let Px' : Finset F := P_x.filter (fun x => Polynomial.Bivariate.evalX x G ≠ 0)
  let Py' : Finset F := P_y.filter (fun y => Polynomial.Bivariate.evalY y G ≠ 0)
  -- card bounds on zeros
  have hcard_zero_x : (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card ≤ gx := by
    simpa [gx] using PS_card_evalX_eq_zero_le_degreeX (A := G) hG0 P_x
  have hcard_zero_y : (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card ≤ gy := by
    simpa [gy] using PS_card_evalY_eq_zero_le_natDegreeY (A := G) hG0 P_y
  -- card lower bounds on filtered sets
  have hcard_Px' : (n_x : ℕ) - gx ≤ Px'.card := by
    have hpart : (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card + Px'.card = P_x.card := by
      simpa [Px'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_x)
          (p := fun x => Polynomial.Bivariate.evalX x G = 0))
    have hPx'_eq : Px'.card = P_x.card - (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card := by
      have := congrArg (fun t => t - (P_x.filter (fun x => Polynomial.Bivariate.evalX x G = 0)).card) hpart
      simpa [Nat.add_sub_cancel_left] using this
    have h1 : (n_x : ℕ) - gx ≤ P_x.card - gx := Nat.sub_le_sub_right h_card_Px gx
    have h2 : P_x.card - gx ≤ Px'.card := by
      simpa [hPx'_eq] using (Nat.sub_le_sub_left hcard_zero_x P_x.card)
    exact le_trans h1 h2
  have hcard_Py' : (n_y : ℕ) - gy ≤ Py'.card := by
    have hpart : (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card + Py'.card = P_y.card := by
      simpa [Py'] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := P_y)
          (p := fun y => Polynomial.Bivariate.evalY y G = 0))
    have hPy'_eq : Py'.card = P_y.card - (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card := by
      have := congrArg (fun t => t - (P_y.filter (fun y => Polynomial.Bivariate.evalY y G = 0)).card) hpart
      simpa [Nat.add_sub_cancel_left] using this
    have h1 : (n_y : ℕ) - gy ≤ P_y.card - gy := Nat.sub_le_sub_right h_card_Py gy
    have h2 : P_y.card - gy ≤ Py'.card := by
      simpa [hPy'_eq] using (Nat.sub_le_sub_left hcard_zero_y P_y.card)
    exact le_trans h1 h2
  -- Nonempty instances for filtered sets
  have hxpos : 0 < Px'.card := lt_of_lt_of_le (Nat.sub_pos_of_lt hx_lt_nx) hcard_Px'
  have hypos : 0 < Py'.card := lt_of_lt_of_le (Nat.sub_pos_of_lt hy_lt_ny) hcard_Py'
  haveI : Nonempty Px' := by
    classical
    rcases Finset.card_pos.mp hxpos with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  haveI : Nonempty Py' := by
    classical
    rcases Finset.card_pos.mp hypos with ⟨y, hy⟩
    exact ⟨⟨y, hy⟩⟩
  -- adjusted parameters
  let ax' : ℕ := a_x - gx
  let ay' : ℕ := a_y - gy
  let bx' : ℕ := b_x - gx
  let by' : ℕ := b_y - gy
  let nx' : ℕ+ := ⟨(n_x : ℕ) - gx, Nat.sub_pos_of_lt hx_lt_nx⟩
  let ny' : ℕ+ := ⟨(n_y : ℕ) - gy, Nat.sub_pos_of_lt hy_lt_ny⟩
  have hbxax' : bx' ≥ ax' := by
    -- bx' ≥ ax' ↔ ax' ≤ bx'
    simpa [bx', ax'] using (Nat.sub_le_sub_right h_bx_ge_ax gx)
  have hbyay' : by' ≥ ay' := by
    simpa [by', ay'] using (Nat.sub_le_sub_right h_by_ge_ay gy)
  -- simplify differences bx' - ax' and by' - ay'
  have hdiff_x : bx' - ax' = b_x - a_x := by
    simpa [bx', ax'] using
      (tsub_tsub_tsub_cancel_right (a := b_x) (b := a_x) (c := gx) hgx_le_ax)
  have hdiff_y : by' - ay' = b_y - a_y := by
    simpa [by', ay'] using
      (tsub_tsub_tsub_cancel_right (a := b_y) (b := a_y) (c := gy) hgy_le_ay)
  -- descend quotient hypotheses to A1,B1
  have hquotX' : ∀ y ∈ Py', (quot_X y).natDegree ≤ (bx' - ax') ∧
      Polynomial.Bivariate.evalY y B1 = (quot_X y) * Polynomial.Bivariate.evalY y A1 := by
    intro y hy
    have hyP : y ∈ P_y := (Finset.mem_filter.mp hy).1
    have hyG : Polynomial.Bivariate.evalY y G ≠ 0 := (Finset.mem_filter.mp hy).2
    have hq := h_quot_X y hyP
    refine ⟨?_, ?_⟩
    · simpa [hdiff_x] using hq.1
    · exact PS_descend_evalY (hA := hA) (hB := hB) y hyG (quot_X y) hq.2
  have hquotY' : ∀ x ∈ Px', (quot_Y x).natDegree ≤ (by' - ay') ∧
      Polynomial.Bivariate.evalX x B1 = (quot_Y x) * Polynomial.Bivariate.evalX x A1 := by
    intro x hx
    have hxP : x ∈ P_x := (Finset.mem_filter.mp hx).1
    have hxG : Polynomial.Bivariate.evalX x G ≠ 0 := (Finset.mem_filter.mp hx).2
    have hq := h_quot_Y x hxP
    refine ⟨?_, ?_⟩
    · simpa [hdiff_y] using hq.1
    · exact PS_descend_evalX (hA := hA) (hB := hB) x hxG (quot_Y x) hq.2
  -- degree bounds for A1,B1 under adjusted parameters
  have h_ax' : ax' ≥ Polynomial.Bivariate.degreeX A1 := by
    have hsum : gx + Polynomial.Bivariate.degreeX A1 ≤ a_x := by
      simpa [hdegX_A] using h_f_degX
    have : Polynomial.Bivariate.degreeX A1 ≤ a_x - gx := le_tsub_of_add_le_left hsum
    simpa [ax', ge_iff_le] using this
  have h_ay' : ay' ≥ Polynomial.Bivariate.natDegreeY A1 := by
    have hsum : gy + Polynomial.Bivariate.natDegreeY A1 ≤ a_y := by
      simpa [hdegY_A] using h_f_degY
    have : Polynomial.Bivariate.natDegreeY A1 ≤ a_y - gy := le_tsub_of_add_le_left hsum
    simpa [ay', ge_iff_le] using this
  have h_bx' : bx' ≥ Polynomial.Bivariate.degreeX B1 := by
    have hsum : gx + Polynomial.Bivariate.degreeX B1 ≤ b_x := by
      simpa [hdegX_B] using h_g_degX
    have : Polynomial.Bivariate.degreeX B1 ≤ b_x - gx := le_tsub_of_add_le_left hsum
    simpa [bx', ge_iff_le] using this
  have h_by' : by' ≥ Polynomial.Bivariate.natDegreeY B1 := by
    have hsum : gy + Polynomial.Bivariate.natDegreeY B1 ≤ b_y := by
      simpa [hdegY_B] using h_g_degY
    have : Polynomial.Bivariate.natDegreeY B1 ≤ b_y - gy := le_tsub_of_add_le_left hsum
    simpa [by', ge_iff_le] using this
  -- card bounds in the form needed (using nx',ny')
  have hcard_Px'' : nx' ≤ Px'.card := by
    simpa [nx'] using hcard_Px'
  have hcard_Py'' : ny' ≤ Py'.card := by
    simpa [ny'] using hcard_Py'
  -- inequality for adjusted ratios
  have hxfrac : (bx' : ℚ) / (nx' : ℚ) ≤ (b_x : ℚ) / (n_x : ℚ) := by
    have hn1 : (0 : ℚ) < (n_x : ℚ) := by
      exact_mod_cast n_x.pos
    have hn2 : (0 : ℚ) < (nx' : ℚ) := by
      exact_mod_cast nx'.pos
    -- use div_le_div_iff₀
    refine (div_le_div_iff₀ hn2 hn1).2 ?_
    -- show (bx')*n_x ≤ b_x*nx'
    have hbx'cast : (bx' : ℚ) = (b_x : ℚ) - (gx : ℚ) := by
      -- bx' = b_x - gx, and gx ≤ b_x
      have : gx ≤ b_x := hgx_le_bx
      simpa [bx', Nat.cast_sub this]
    have hnx'cast : (nx' : ℚ) = (n_x : ℚ) - (gx : ℚ) := by
      have : gx ≤ (n_x : ℕ) := le_of_lt hx_lt_nx
      simpa [nx', Nat.cast_sub this]
    -- start from gx*b_x ≤ gx*n_x
    have hbn : (b_x : ℚ) ≤ (n_x : ℚ) := by
      exact_mod_cast (le_of_lt hbxltnx)
    have hgx_nonneg : (0 : ℚ) ≤ (gx : ℚ) := by
      exact_mod_cast (Nat.zero_le gx)
    have hmul : (gx : ℚ) * (b_x : ℚ) ≤ (gx : ℚ) * (n_x : ℚ) :=
      mul_le_mul_of_nonneg_left hbn hgx_nonneg
    have hsub : (b_x : ℚ) * (n_x : ℚ) - (gx : ℚ) * (n_x : ℚ) ≤
        (b_x : ℚ) * (n_x : ℚ) - (gx : ℚ) * (b_x : ℚ) := by
      -- subtract the inequality from (b_x*n_x)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (sub_le_sub_left hmul ((b_x : ℚ) * (n_x : ℚ)))
    -- rewrite into the desired form
    rw [hbx'cast, hnx'cast]
    simpa [sub_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hsub
  have hyfrac : (by' : ℚ) / (ny' : ℚ) ≤ (b_y : ℚ) / (n_y : ℚ) := by
    have hn1 : (0 : ℚ) < (n_y : ℚ) := by
      exact_mod_cast n_y.pos
    have hn2 : (0 : ℚ) < (ny' : ℚ) := by
      exact_mod_cast ny'.pos
    refine (div_le_div_iff₀ hn2 hn1).2 ?_
    have hby'cast : (by' : ℚ) = (b_y : ℚ) - (gy : ℚ) := by
      have : gy ≤ b_y := hgy_le_by
      simpa [by', Nat.cast_sub this]
    have hny'cast : (ny' : ℚ) = (n_y : ℚ) - (gy : ℚ) := by
      have : gy ≤ (n_y : ℕ) := le_of_lt hy_lt_ny
      simpa [ny', Nat.cast_sub this]
    have hbn : (b_y : ℚ) ≤ (n_y : ℚ) := by
      exact_mod_cast (le_of_lt hbyltny)
    have hgy_nonneg : (0 : ℚ) ≤ (gy : ℚ) := by
      exact_mod_cast (Nat.zero_le gy)
    have hmul : (gy : ℚ) * (b_y : ℚ) ≤ (gy : ℚ) * (n_y : ℚ) :=
      mul_le_mul_of_nonneg_left hbn hgy_nonneg
    have hsub : (b_y : ℚ) * (n_y : ℚ) - (gy : ℚ) * (n_y : ℚ) ≤
        (b_y : ℚ) * (n_y : ℚ) - (gy : ℚ) * (b_y : ℚ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (sub_le_sub_left hmul ((b_y : ℚ) * (n_y : ℚ)))
    rw [hby'cast, hny'cast]
    simpa [sub_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hsub
  have h_le_1' : (1 : ℚ) > (bx' : ℚ) / (nx' : ℚ) + (by' : ℚ) / (ny' : ℚ) := by
    have hsum_le : (bx' : ℚ) / (nx' : ℚ) + (by' : ℚ) / (ny' : ℚ) ≤
        (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ) := by
      exact add_le_add hxfrac hyfrac
    exact lt_of_le_of_lt hsum_le h_le_1
  -- apply coprime-case lemma to A1,B1
  have hconst : Polynomial.Bivariate.degreeX A1 = 0 ∧ Polynomial.Bivariate.natDegreeY A1 = 0 := by
    classical
    simpa [ax', ay', bx', by', nx', ny'] using
      (PS_coprime_case_constant (F := F) ax' ay' bx' by' nx' ny' hbxax' hbyay' A1 B1
        hA1 hB1 hrel h_ax' h_bx' h_ay' h_by'
        Px' Py' quot_X quot_Y hcard_Px'' hcard_Py''
        hquotX' hquotY' h_le_1')
  -- get B1 = P1 * A1
  rcases PS_exists_P_of_degreeX_eq_zero_natDegreeY_eq_zero (A := A1) (B := B1) hA1 hconst.1 hconst.2 with
    ⟨P1, hB1fac⟩
  refine ⟨P1, ?_⟩
  -- assemble
  calc
    B = G * B1 := by
      simpa [hB]
    _ = G * (P1 * A1) := by
      simpa [hB1fac]
    _ = P1 * (G * A1) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = P1 * A := by
      simpa [hA]


theorem PS_exists_P {F : Type} [Field F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (A B : F[X][Y])
  (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A) (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
  (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A) (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧
      Polynomial.Bivariate.evalY y B = (quot_X y) * (Polynomial.Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧
      Polynomial.Bivariate.evalX x B = (quot_Y x) * (Polynomial.Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  : ∃ P : F[X][Y], B = P * A := by
  classical
  letI : DecidableEq F := Classical.decEq F

  by_cases hB0 : B = 0
  · refine ⟨0, ?_⟩
    simp [hB0]
  · have hB : B ≠ 0 := hB0
    by_cases hA0 : A = 0
    · have hA : A = 0 := hA0

      have hBx_lt : b_x < (n_x : ℕ) :=
        PS_bx_lt_nx (b_x := b_x) (b_y := b_y) (n_x := n_x) (n_y := n_y) h_le_1
      have hBx_lt_card : b_x < P_x.card := lt_of_lt_of_le hBx_lt h_card_Px

      have h_evalX_B_zero : ∀ x ∈ P_x, Polynomial.Bivariate.evalX x B = 0 := by
        intro x hx
        have hEq :
            Polynomial.Bivariate.evalX x B =
              (quot_Y x) * (Polynomial.Bivariate.evalX x A) :=
          (h_quot_Y x hx).2
        simpa [hA, PS_evalX_eq_map] using hEq

      have hB_eq : B = 0 := by
        by_contra hB_ne

        have hcard_le :
            (P_x.filter (fun x => Polynomial.Bivariate.evalX x B = 0)).card ≤
              Polynomial.Bivariate.degreeX B :=
          PS_card_evalX_eq_zero_le_degreeX (A := B) hB_ne P_x

        have hfilter_eq :
            P_x.filter (fun x => Polynomial.Bivariate.evalX x B = 0) = P_x := by
          ext x
          by_cases hx : x ∈ P_x
          · simp [Finset.mem_filter, hx, h_evalX_B_zero x hx]
          · simp [Finset.mem_filter, hx]

        have hPx_card_le : P_x.card ≤ Polynomial.Bivariate.degreeX B := by
          simpa [hfilter_eq] using hcard_le

        have hdegX_le : Polynomial.Bivariate.degreeX B ≤ b_x := by
          exact h_g_degX
        have hdegX_lt : Polynomial.Bivariate.degreeX B < P_x.card :=
          lt_of_le_of_lt hdegX_le hBx_lt_card

        exact (not_lt_of_ge hPx_card_le) hdegX_lt

      refine ⟨0, ?_⟩
      simp [hB_eq, hA]

    · have hA : A ≠ 0 := hA0
      exact
        PS_exists_P_nonzero (a_x := a_x) (a_y := a_y) (b_x := b_x) (b_y := b_y)
          (n_x := n_x) (n_y := n_y) (h_bx_ge_ax := h_bx_ge_ax) (h_by_ge_ay := h_by_ge_ay)
          (A := A) (B := B) (hA0 := hA) (hB0 := hB) (h_f_degX := h_f_degX)
          (h_g_degX := h_g_degX) (h_f_degY := h_f_degY) (h_g_degY := h_g_degY)
          (P_x := P_x) (P_y := P_y) (quot_X := quot_X) (quot_Y := quot_Y)
          (h_card_Px := h_card_Px) (h_card_Py := h_card_Py) (h_quot_X := h_quot_X)
          (h_quot_Y := h_quot_Y) (h_le_1 := h_le_1)

theorem Polishchuk_Spielman {F : Type} [Field F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (A B : F[X][Y])
  (hA0 : A ≠ 0)
  (h_f_degX : a_x ≥ Polynomial.Bivariate.degreeX A) (h_g_degX : b_x ≥ Polynomial.Bivariate.degreeX B)
  (h_f_degY : a_y ≥ Polynomial.Bivariate.natDegreeY A) (h_g_degY : b_y ≥ Polynomial.Bivariate.natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧ Polynomial.Bivariate.evalY y B = (quot_X y) * (Polynomial.Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧ Polynomial.Bivariate.evalX x B = (quot_Y x) * (Polynomial.Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  : ∃ P : F[X][Y], B = P * A
    ∧ Polynomial.Bivariate.degreeX P ≤ b_x - a_x ∧ Polynomial.Bivariate.natDegreeY P ≤ b_y - a_y
    ∧ (∃ Q_x : Finset F, Q_x.card ≥ (n_x : ℕ) - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Polynomial.Bivariate.evalX x P = quot_Y x)
    ∧ (∃ Q_y : Finset F, Q_y.card ≥ (n_y : ℕ) - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Polynomial.Bivariate.evalY y P = quot_X y) := by
  classical
  letI : DecidableEq F := Classical.decEq F

  -- 1. obtain P with B = P * A
  obtain ⟨P, hBA⟩ :=
    PS_exists_P (F := F) a_x a_y b_x b_y n_x n_y h_bx_ge_ax h_by_ge_ay A B
      h_f_degX h_g_degX h_f_degY h_g_degY P_x P_y quot_X quot_Y h_card_Px h_card_Py h_quot_X
      h_quot_Y h_le_1

  -- 2. degree bounds for P
  have hdeg : Polynomial.Bivariate.degreeX P ≤ b_x - a_x ∧
      Polynomial.Bivariate.natDegreeY P ≤ b_y - a_y :=
    PS_degree_bounds_of_mul (F := F) a_x a_y b_x b_y n_x n_y h_bx_ge_ax h_by_ge_ay
      (A := A) (B := B) (P := P) hA0 hBA h_f_degX h_g_degX h_f_degY h_g_degY P_x P_y
      quot_X quot_Y h_card_Px h_card_Py h_quot_X h_quot_Y h_le_1

  -- 3. cancellation in X gives Q_x
  have h_quot_Y_eq : ∀ x ∈ P_x, Polynomial.Bivariate.evalX x B = (quot_Y x) * Polynomial.Bivariate.evalX x A := by
    intro x hx
    exact (h_quot_Y x hx).2

  obtain ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩ :=
    PS_exists_Qx_of_cancel (F := F) a_x n_x (A := A) (B := B) (P := P) hA0 hBA P_x h_card_Px
      quot_Y h_quot_Y_eq h_f_degX

  -- 4. cancellation in Y gives Q_y
  have h_quot_X_eq : ∀ y ∈ P_y, Polynomial.Bivariate.evalY y B = (quot_X y) * Polynomial.Bivariate.evalY y A := by
    intro y hy
    exact (h_quot_X y hy).2

  obtain ⟨Q_y, hQy_card, hQy_sub, hQy_eval⟩ :=
    PS_exists_Qy_of_cancel (F := F) a_y n_y (A := A) (B := B) (P := P) hA0 hBA P_y h_card_Py
      quot_X h_quot_X_eq h_f_degY

  -- assemble
  refine ⟨P, hBA, hdeg.1, hdeg.2, ?_, ?_⟩
  · exact ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩
  · exact ⟨Q_y, hQy_card, hQy_sub, hQy_eval⟩

