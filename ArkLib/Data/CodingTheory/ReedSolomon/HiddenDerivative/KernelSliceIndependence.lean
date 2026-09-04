/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.LocalConstraintKernel
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Independence of the exhibited local-kernel slices

This file proves the `T`-adic independence used to combine the exhibited kernel slices. The
argument views a local multivariate polynomial as a univariate polynomial in `T`. A source
polynomial with no `T` has only a constant coefficient, while the constant coefficient of the
hidden error `U - localJetSum` is `U - Y₁`. Thus a nonzero element in the slice indexed by `r`
has lowest `T`-coefficient `(U - Y₁)^h * G`, which is nonzero over a field.

Only the exhibited subspace of the kernel is counted here. No reverse kernel inclusion or rank
equality is asserted.
-/

noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {F : Type*} [Field F]
variable {d m : ℕ}

/-- The coefficient of `T^n`, with all remaining local variables kept as multivariate
polynomial variables. -/
def localTCoefficient (d n : ℕ) (P : LocalPolynomial F d) :
    MvPolynomial (Option (Fin d)) F :=
  Polynomial.coeff (MvPolynomial.optionEquivLeft F (Option (Fin d)) P) n

/-- A local polynomial has no `T` when every monomial in its support has `T`-exponent zero. -/
def IsLocalTFree (P : LocalPolynomial F d) : Prop :=
  ∀ e ∈ P.support, e (localT d) = 0

@[simp]
theorem localTCoefficient_zero (d n : ℕ) :
    localTCoefficient (F := F) d n 0 = 0 := by
  simp [localTCoefficient]

theorem localTCoefficient_add (d n : ℕ) (P Q : LocalPolynomial F d) :
    localTCoefficient d n (P + Q) = localTCoefficient d n P + localTCoefficient d n Q := by
  simp [localTCoefficient]

theorem localTCoefficient_sum {I : Type*} (s : Finset I)
    (P : I → LocalPolynomial F d) (n : ℕ) :
    localTCoefficient d n (s.sum P) = s.sum fun i ↦ localTCoefficient d n (P i) := by
  simp [localTCoefficient]

/-- Truncation modulo `T^m` preserves exactly the coefficients of degree below `m`. -/
theorem localTCoefficient_truncateLocalT (P : LocalPolynomial F d) (n : ℕ) :
    localTCoefficient d n (truncateLocalT (R := F) (d := d) m P) =
      if n < m then localTCoefficient d n P else 0 := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases hn : n < m
  · simp only [hn, if_true, localTCoefficient]
    rw [MvPolynomial.optionEquivLeft_coeff_coeff,
      MvPolynomial.optionEquivLeft_coeff_coeff,
      truncateLocalT, coeff_filterLocalMonomials]
    simp [localT, hn]
  · simp only [hn, if_false, localTCoefficient, coeff_zero]
    rw [MvPolynomial.optionEquivLeft_coeff_coeff,
      truncateLocalT, coeff_filterLocalMonomials]
    simp [localT, hn]

/-- The zeroth `T`-coefficient detects a `T`-free polynomial. -/
theorem localTCoefficient_zero_injective_on_tFree
    {P : LocalPolynomial F d} (hfree : IsLocalTFree P)
    (hcoeff : localTCoefficient d 0 P = 0) : P = 0 := by
  apply MvPolynomial.ext
  intro e
  by_cases heT : e (localT d) = 0
  · have hc := congrArg (MvPolynomial.coeff e.some) hcoeff
    rw [localTCoefficient, MvPolynomial.optionEquivLeft_coeff_coeff] at hc
    have heNone : e none = 0 := by simpa [localT] using heT
    rw [← heNone, Finsupp.optionElim_some] at hc
    exact hc
  · have hnotmem : e ∉ P.support := by
      intro he
      exact heT (hfree e he)
    simpa [MvPolynomial.mem_support_iff] using hnotmem

/-- The constant coefficient of the visible-jet sum is `Y₁`. -/
theorem localTCoefficient_zero_localJetSum (hd : 0 < d) :
    localTCoefficient (F := F) d 0 (localJetSum d) =
      X (some (⟨0, hd⟩ : Fin d)) := by
  classical
  let j₀ : Fin d := ⟨0, hd⟩
  rw [localJetSum, localTCoefficient_sum Finset.univ _ 0, Finset.sum_eq_single j₀]
  · simp [localTCoefficient, localT, localY, j₀]
  · intro j _ hj
    have hjval : j.val ≠ 0 := by
      intro hval
      apply hj
      exact Fin.ext hval
    simp [localTCoefficient, localT, localY]
    intro hzero
    exact (hjval hzero.symm).elim
  · simp

/-- The constant coefficient of the hidden error is the nonzero polynomial `U - Y₁`. -/
theorem localTCoefficient_zero_hiddenErrorFactor (hd : 0 < d) :
    localTCoefficient (F := F) d 0 (hiddenErrorFactor d) =
      X none - X (some (⟨0, hd⟩ : Fin d)) := by
  rw [hiddenErrorFactor, localTCoefficient]
  simp only [map_sub, Polynomial.coeff_sub]
  change localTCoefficient d 0 (X (localU d)) -
      localTCoefficient d 0 (localJetSum d) = _
  rw [show (localU d) = some none by rfl]
  rw [localTCoefficient_zero_localJetSum (F := F) hd]
  simp [localTCoefficient]

theorem localTCoefficient_zero_hiddenErrorFactor_ne_zero (hd : 0 < d) :
    localTCoefficient (F := F) d 0 (hiddenErrorFactor d) ≠ 0 := by
  rw [localTCoefficient_zero_hiddenErrorFactor hd]
  intro h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single none 1)) h
  simp at hc

/-- The lowest `T`-coefficient of an exhibited slice is multiplication by a nonzero power of
`U - Y₁`; it therefore detects every nonzero `T`-free source polynomial. -/
theorem localTCoefficient_exhibitedKernelFactor_mul_eq_zero_iff
    (hd : 0 < d) (r h : ℕ) (G : LocalPolynomial F d) (hfree : IsLocalTFree G) :
    localTCoefficient d r (exhibitedKernelFactor d r h * G) = 0 ↔ G = 0 := by
  rw [exhibitedKernelFactor]
  change Polynomial.coeff
      (MvPolynomial.optionEquivLeft F (Option (Fin d))
        (X (localT d) ^ r * hiddenErrorFactor d ^ h * G)) r = 0 ↔ _
  rw [map_mul, map_mul, map_pow]
  simp only [localT, MvPolynomial.optionEquivLeft_X_none, map_pow]
  rw [mul_assoc]
  have hcoeff : Polynomial.coeff
      (Polynomial.X ^ r *
        ((MvPolynomial.optionEquivLeft F (Option (Fin d)) (hiddenErrorFactor d)) ^ h *
          MvPolynomial.optionEquivLeft F (Option (Fin d)) G)) r =
      Polynomial.coeff
        ((MvPolynomial.optionEquivLeft F (Option (Fin d)) (hiddenErrorFactor d)) ^ h *
          MvPolynomial.optionEquivLeft F (Option (Fin d)) G) 0 := by
    simpa using Polynomial.coeff_X_pow_mul
      ((MvPolynomial.optionEquivLeft F (Option (Fin d)) (hiddenErrorFactor d)) ^ h *
        MvPolynomial.optionEquivLeft F (Option (Fin d)) G) r 0
  rw [hcoeff]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_pow,
    ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hfactor | hG
    · exact ((pow_ne_zero h
          (localTCoefficient_zero_hiddenErrorFactor_ne_zero (F := F) hd)) hfactor).elim
    · exact localTCoefficient_zero_injective_on_tFree hfree hG
  · rintro rfl
    simp

/-- A slice indexed by `r` has no `T`-coefficient below `r`. -/
theorem localTCoefficient_exhibitedKernelFactor_mul_eq_zero_of_lt
    (r h n : ℕ) (G : LocalPolynomial F d) (hnr : n < r) :
    localTCoefficient d n (exhibitedKernelFactor d r h * G) = 0 := by
  rw [exhibitedKernelFactor]
  change Polynomial.coeff
      (MvPolynomial.optionEquivLeft F (Option (Fin d))
        (X (localT d) ^ r * hiddenErrorFactor d ^ h * G)) n = 0
  rw [map_mul, map_mul, map_pow]
  simp only [localT, MvPolynomial.optionEquivLeft_X_none, map_pow]
  rw [mul_assoc, Polynomial.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hnr]

/-- A finite sum of exhibited slices remains independent after reduction modulo `T^m`. The
threshold may vary arbitrarily with the slice; the canonical contact threshold is a later
specialization. -/
theorem truncateLocalT_sum_exhibitedKernelFactor_mul_eq_zero_iff
    (hd : 0 < d) (h : Fin m → ℕ) (G : Fin m → LocalPolynomial F d)
    (hfree : ∀ r, IsLocalTFree (G r)) :
    truncateLocalT (R := F) (d := d) m
        (∑ r : Fin m, exhibitedKernelFactor d r.val (h r) * G r) = 0 ↔
      ∀ r, G r = 0 := by
  constructor
  · intro hsum
    have hzero : ∀ n, n < m → ∀ r : Fin m, r.val = n → G r = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro hn r hr
          subst n
          have hc := congrArg (localTCoefficient (F := F) d r.val) hsum
          rw [localTCoefficient_truncateLocalT, if_pos hn,
            localTCoefficient_zero, localTCoefficient_sum] at hc
          have hother : ∀ s : Fin m, s ≠ r →
              localTCoefficient d r.val
                (exhibitedKernelFactor d s.val (h s) * G s) = 0 := by
            intro s hsr
            have hvalne : s.val ≠ r.val := Fin.val_ne_of_ne hsr
            rcases lt_or_gt_of_ne hvalne with hslt | hsgt
            · have hs0 : G s = 0 := ih s.val hslt s.isLt s rfl
              simp [hs0]
            · exact localTCoefficient_exhibitedKernelFactor_mul_eq_zero_of_lt
                s.val (h s) r.val (G s) hsgt
          have hrzero : localTCoefficient d r.val
              (exhibitedKernelFactor d r.val (h r) * G r) = 0 := by
            rw [Finset.sum_eq_single r] at hc
            · exact hc
            · intro s _ hsr
              exact hother s hsr
            · simp
          exact (localTCoefficient_exhibitedKernelFactor_mul_eq_zero_iff
            hd r.val (h r) (G r) (hfree r)).mp hrzero
    intro r
    exact hzero r.val r.isLt r rfl
  · intro hG
    simp [hG]

end ReedSolomon.HiddenDerivative
