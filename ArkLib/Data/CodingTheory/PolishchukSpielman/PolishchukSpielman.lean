/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.PolishchukSpielman.Degrees
import ArkLib.Data.CodingTheory.PolishchukSpielman.Existence
import ArkLib.Data.CodingTheory.PolishchukSpielman.Resultant

/-!
# Polishchuk-Spielman algorithm

This file defines the main theorem for the Polishchuk-Spielman algorithm,
which provides an efficient decoding method for Reed-Solomon codes.

## Main results

- `polishchuk_spielman`: The main theorem stating the existence of the
  interpolating polynomial $Q(X, Y)$ and the error locator polynomial $E(X)$.

## References

* [Polishchuk, A., and Spielman, D., *Holographic proofs of high-degree polynomials*][PS94]
* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]

-/

open Polynomial.Bivariate Polynomial Matrix
open scoped BigOperators

theorem polishchuk_spielman {F : Type} [Field F]
    (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
    (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
    (A B : F[X][Y])
    (hA0 : A ≠ 0)
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
    (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ)) :
    ∃ P : F[X][Y], B = P * A
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
      (A := A) (B := B) (P := P) hA0 hBA h_f_degX h_f_degY h_g_degY P_x P_y
      quot_X quot_Y h_card_Px h_card_Py h_quot_X h_quot_Y h_le_1

  -- 3. cancellation in X gives Q_x
  have h_quot_Y_eq :
  ∀ x ∈ P_x, Polynomial.Bivariate.evalX x B = (quot_Y x) * Polynomial.Bivariate.evalX x A := by
    intro x hx
    exact (h_quot_Y x hx).2

  obtain ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩ :=
    PS_exists_Qx_of_cancel (F := F) a_x n_x (A := A) (B := B) (P := P) hA0 hBA P_x h_card_Px
      quot_Y h_quot_Y_eq h_f_degX

  -- 4. cancellation in Y gives Q_y
  have h_quot_X_eq :
  ∀ y ∈ P_y, Polynomial.Bivariate.evalY y B = (quot_X y) * Polynomial.Bivariate.evalY y A := by
    intro y hy
    exact (h_quot_X y hy).2

  obtain ⟨Q_y, hQy_card, hQy_sub, hQy_eval⟩ :=
    PS_exists_Qy_of_cancel (F := F) a_y n_y (A := A) (B := B) (P := P) hA0 hBA P_y h_card_Py
      quot_X h_quot_X_eq h_f_degY

  -- assemble
  refine ⟨P, hBA, hdeg.1, hdeg.2, ?_, ?_⟩
  · exact ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩
  · exact ⟨Q_y, hQy_card, hQy_sub, hQy_eval⟩
