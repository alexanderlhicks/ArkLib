import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Group.Basic

open Polynomial
open Ideal
open BCIKS20AppendixA
open ToRatFunc
open Polynomial.Bivariate
open BCIKS20AppendixA.ClaimA2
open scoped BigOperators

noncomputable def T_def {F : Type} [CommRing F] [IsDomain F]
    (H : Polynomial (Polynomial F)) : BCIKS20AppendixA.𝕃 (F := F) H :=
  Ideal.Quotient.mk (Ideal.span {BCIKS20AppendixA.H_tilde (F := F) H}) Polynomial.X

noncomputable def W_def {F : Type} [CommRing F] [IsDomain F]
    (H : Polynomial (Polynomial F)) : BCIKS20AppendixA.𝕃 (F := F) H :=
  BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) (Polynomial.leadingCoeff H)

theorem embeddingOf𝒪Into𝕃_mk {F : Type} [CommRing F] [IsDomain F]
  (H : Polynomial (Polynomial F)) (q : Polynomial (Polynomial F)) :
  BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (F := F) H
      (Ideal.Quotient.mk (Ideal.span {BCIKS20AppendixA.H_tilde' (F := F) H}) q)
    =
    Ideal.Quotient.mk (Ideal.span {BCIKS20AppendixA.H_tilde (F := F) H})
      (ToRatFunc.bivPolyHom (F := F) q) := by
  simp [BCIKS20AppendixA.embeddingOf𝒪Into𝕃]

theorem embeddingOf𝒪Into𝕃_C {F : Type} [CommRing F] [IsDomain F]
  (H : Polynomial (Polynomial F)) (a : Polynomial F) :
  BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (F := F) H
      (Ideal.Quotient.mk (Ideal.span {BCIKS20AppendixA.H_tilde' (F := F) H}) (Polynomial.C a))
    =
    BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) a := by
  classical
  -- Apply the computation lemma for `Ideal.Quotient.mk`.
  simpa [embeddingOf𝒪Into𝕃_mk, BCIKS20AppendixA.liftToFunctionField,
    BCIKS20AppendixA.coeffAsRatFunc]

theorem evalX_coeff {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (n : ℕ) :
  (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).coeff n
    =
    Polynomial.eval (Polynomial.C x₀) (R.coeff n) := by
  simp [Polynomial.Bivariate.evalX, Polynomial.coeff]

theorem evalX_derivative_comm {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) :
  Polynomial.Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)
    =
    Polynomial.derivative (Polynomial.Bivariate.evalX (Polynomial.C x₀) R) := by
  classical
  ext n m
  -- rewrite everything using `evalRingHom` so we can use `map_mul`
  -- and unfold the two `evalX` occurrences
  simp [Polynomial.Bivariate.evalX, Polynomial.coeff_derivative, Polynomial.toFinsupp_apply, Polynomial.eval, Polynomial.eval₂]


theorem evalX_zero {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) :
  Polynomial.Bivariate.evalX (Polynomial.C x₀)
      (0 : Polynomial (Polynomial (Polynomial F)))
    =
    (0 : Polynomial (Polynomial F)) := by
  ext n
  simp [evalX_coeff]


theorem leadingCoeff_divides_topCoeff_of_evalX_derivative {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  (hRH : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
  (hd : 0 < Polynomial.natDegree R) :
  H.leadingCoeff ∣
    (Polynomial.Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)).coeff
      (Polynomial.natDegree R - 1) := by
  classical
  -- Let P be R evaluated in the X-variable
  set P : Polynomial (Polynomial F) := Polynomial.Bivariate.evalX (Polynomial.C x₀) R
  have hRH' : H ∣ P := by
    simpa [P] using hRH
  have hLC : H.leadingCoeff ∣ P.leadingCoeff := by
    simpa using (Polynomial.leadingCoeff_dvd_leadingCoeff hRH')

  -- Set d = natDegree R (this also rewrites the goal to use `d`)
  set d : ℕ := Polynomial.natDegree R with hd_def
  have hd' : 0 < d := by
    -- unfold d
    simpa [d] using hd

  have h1le : 1 ≤ d := Nat.succ_le_iff.mp hd'

  -- Commute evalX and derivative
  have hderiv :
      Polynomial.Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)
        =
        Polynomial.derivative P := by
    simpa [P] using (evalX_derivative_comm (F := F) x₀ R)

  -- Rewrite the goal in terms of P
  rw [hderiv]

  -- coefficient formula for the derivative at degree d-1
  have hcoeff : (Polynomial.derivative P).coeff (d - 1) = P.coeff d * (↑(d - 1) + 1) := by
    -- `coeff_derivative` gives `(derivative P).coeff n = P.coeff (n+1) * (n+1)`
    -- and `simp` rewrites the scalar `↑(n+1)` as `↑n + 1`.
    simpa [Nat.sub_add_cancel h1le] using (Polynomial.coeff_derivative P (d - 1))

  -- Split on whether the top coefficient of P vanishes.
  by_cases h0 : P.coeff d = 0
  · -- If the coefficient is 0, then the derivative coefficient is 0.
    have : H.leadingCoeff ∣ 0 := dvd_zero _
    simpa [hcoeff, h0] using this
  · -- Otherwise, identify natDegree P with d so that leadingCoeff P = coeff P d.
    have hPdeg_le : P.natDegree ≤ d := by
      refine (Polynomial.natDegree_le_iff_coeff_eq_zero).2 ?_
      intro N hNd
      -- coefficients above d vanish in R
      have hRcoeff : R.coeff N = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        -- natDegree R = d < N
        simpa [d] using hNd
      -- evaluate coefficientwise
      have hPN : P.coeff N = Polynomial.eval (Polynomial.C x₀) (R.coeff N) := by
        simpa [P] using (evalX_coeff (F := F) x₀ R N)
      rw [hPN, hRcoeff]
      simp

    have hPdeg_ge : d ≤ P.natDegree :=
      Polynomial.le_natDegree_of_ne_zero h0

    have hPdeg : P.natDegree = d := le_antisymm hPdeg_le hPdeg_ge

    have hPlc : P.leadingCoeff = P.coeff d := by
      -- `leadingCoeff` is the coefficient at `natDegree`
      simpa [Polynomial.leadingCoeff, hPdeg]

    have hHd : H.leadingCoeff ∣ P.coeff d := by
      -- from divisibility of leading coefficients
      simpa [hPlc] using hLC

    have hmul : H.leadingCoeff ∣ P.coeff d * (↑(d - 1) + 1) :=
      dvd_mul_of_dvd_left hHd _

    -- finish by rewriting the desired coefficient using hcoeff
    simpa [hcoeff] using hmul

theorem ζ_eq_eval₂ {F : Type} [CommRing F] [IsDomain F]
  (R : Polynomial (Polynomial (Polynomial F))) (x₀ : F) (H : Polynomial (Polynomial F))
  [Fact (Irreducible H)] :
  BCIKS20AppendixA.ClaimA2.ζ (F := F) R x₀ H
    =
    let W : BCIKS20AppendixA.𝕃 (F := F) H :=
      BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) (Polynomial.leadingCoeff H)
    let T : BCIKS20AppendixA.𝕃 (F := F) H :=
      Ideal.Quotient.mk (Ideal.span {BCIKS20AppendixA.H_tilde (F := F) H}) Polynomial.X
    Polynomial.eval₂ (BCIKS20AppendixA.liftToFunctionField (F := F) (H := H)) (T / W)
      (Polynomial.Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)) := by
  simp [BCIKS20AppendixA.ClaimA2.ζ]

theorem ξ_regular_natDegree_ge_two {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [H_irreducible : Fact (Irreducible H)]
  (hRH : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
  (hd2 : 2 ≤ Polynomial.natDegree R) :
  ∃ pre : BCIKS20AppendixA.𝒪 (F := F) H,
    let d := Polynomial.natDegree R
    let W : BCIKS20AppendixA.𝕃 (F := F) H :=
      BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) (Polynomial.leadingCoeff H)
    BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (F := F) H pre =
      W ^ (d - 2) * BCIKS20AppendixA.ClaimA2.ζ (F := F) R x₀ H := by
  classical
  simpa using (BCIKS20AppendixA.ClaimA2.ξ_regular (x₀ := x₀) (R := R) (H := H))


theorem ξ_regular_natDegree_one {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [H_irreducible : Fact (Irreducible H)]
  (hRH : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
  (hd : Polynomial.natDegree R = 1) :
  ∃ pre : BCIKS20AppendixA.𝒪 (F := F) H,
    let d := Polynomial.natDegree R
    let W : BCIKS20AppendixA.𝕃 (F := F) H :=
      BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) (Polynomial.leadingCoeff H)
    BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (F := F) H pre =
      W ^ (d - 2) * BCIKS20AppendixA.ClaimA2.ζ (F := F) R x₀ H := by
  classical
  let p : Polynomial (Polynomial F) :=
    Polynomial.Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)
  have hpdef :
      p =
        Polynomial.Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R) := rfl
  have hdeg : (Polynomial.derivative R).natDegree ≤ 0 := by
    have h := Polynomial.natDegree_derivative_le (p := R)
    simpa [hd] using h
  have hpconst : p = Polynomial.C (p.coeff 0) := by
    ext n
    cases n with
    | zero =>
        simp
    | succ n =>
        have hlt : (Polynomial.derivative R).natDegree < Nat.succ n := by
          exact lt_of_le_of_lt hdeg (Nat.succ_pos n)
        have hcoeff : (Polynomial.derivative R).coeff (Nat.succ n) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt
        have hpcoeff :
            p.coeff (Nat.succ n) =
              Polynomial.eval (Polynomial.C x₀)
                ((Polynomial.derivative R).coeff (Nat.succ n)) := by
          simpa [p] using
            (evalX_coeff (F := F) (x₀ := x₀) (R := Polynomial.derivative R) (n := Nat.succ n))
        rw [hpcoeff, hcoeff]
        simp
  refine
    ⟨Ideal.Quotient.mk (Ideal.span {BCIKS20AppendixA.H_tilde' (F := F) H})
        (Polynomial.C (p.coeff 0)), ?_⟩
  simp [hd]
  rw [embeddingOf𝒪Into𝕃_C (F := F) (H := H) (a := p.coeff 0)]
  rw [ζ_eq_eval₂ (F := F) (R := R) (x₀ := x₀) (H := H)]
  rw [← hpdef]
  rw [hpconst]
  simp

theorem ξ_regular_natDegree_zero {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [H_irreducible : Fact (Irreducible H)]
  (hRH : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R)
  (hd : Polynomial.natDegree R = 0) :
  ∃ pre : BCIKS20AppendixA.𝒪 (F := F) H,
    let d := Polynomial.natDegree R
    let W : BCIKS20AppendixA.𝕃 (F := F) H :=
      BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) (Polynomial.leadingCoeff H)
    BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (F := F) H pre =
      W ^ (d - 2) * BCIKS20AppendixA.ClaimA2.ζ (F := F) R x₀ H := by
  classical
  refine ⟨0, ?_⟩
  simp [hd, ζ_eq_eval₂, Polynomial.derivative_of_natDegree_zero hd, Polynomial.Bivariate.evalX]

theorem ξ_regular {F : Type} [CommRing F] [IsDomain F]
  (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) (H : Polynomial (Polynomial F))
  [H_irreducible : Fact (Irreducible H)]
  (hRH : H ∣ Polynomial.Bivariate.evalX (Polynomial.C x₀) R) :
  ∃ pre : BCIKS20AppendixA.𝒪 (F := F) H,
    let d := Polynomial.natDegree R
    let W : BCIKS20AppendixA.𝕃 (F := F) H :=
      BCIKS20AppendixA.liftToFunctionField (F := F) (H := H) (Polynomial.leadingCoeff H)
    BCIKS20AppendixA.embeddingOf𝒪Into𝕃 (F := F) H pre =
      W ^ (d - 2) * BCIKS20AppendixA.ClaimA2.ζ (F := F) R x₀ H := by
  classical
  cases hd : Polynomial.natDegree R with
  | zero =>
      -- d = 0
      simpa [hd] using
        (ξ_regular_natDegree_zero (F := F) (x₀ := x₀) (R := R) (H := H) hRH hd)
  | succ d1 =>
      cases d1 with
      | zero =>
          -- d = 1
          have hd1 : Polynomial.natDegree R = 1 := by
            simpa [hd]
          simpa [hd] using
            (ξ_regular_natDegree_one (F := F) (x₀ := x₀) (R := R) (H := H) hRH hd1)
      | succ d2 =>
          -- d ≥ 2
          have hd2 : 2 ≤ Polynomial.natDegree R := by
            simpa [hd] using (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d2)))
          simpa [hd] using
            (ξ_regular_natDegree_ge_two (F := F) (x₀ := x₀) (R := R) (H := H) hRH hd2)

