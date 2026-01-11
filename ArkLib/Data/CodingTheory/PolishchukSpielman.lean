/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.Polynomial.Bivariate

open Polynomial.Bivariate Polynomial

/--
Polishchuk-Spielman Lemma variant from Ben-Sasson et Al. Proximity Gaps for Reed-Solomon Codes

Hints for the AI Prover:

1.  **Symmetry**: The problem is symmetric with respect to X and Y.
    Consider defining a `swap` map `F[X][Y] → F[X][Y]` that swaps variables, to avoid duplicating arguments.
    Note that `F[X][Y]` is `Polynomial (Polynomial F)`. Swapping involves `eval₂` or similar.

2.  **Resultant**: The proof relies on the Resultant of A and B (viewed as univariate polynomials in Y with coefficients in F[X], or vice versa).
    Use `Polynomial.resultant A B`.

3.  **Degree Bound**:
    Prove that `(resultant A B).natDegree ≤ (natDegreeY A) * (degreeX B) + (natDegreeY B) * (degreeX A)`.
    (Note: `degreeX` is the degree of coefficients in F[X]).
    This follows from the definition of Resultant as the determinant of the Sylvester matrix.

4.  **Multiplicity of Roots**:
    The core of the proof is showing that `resultant A B` vanishes with high multiplicity at points in `P_x`.
    Specifically, for `x ∈ P_x`, if `B(x, Y) = Q(Y) * A(x, Y)` (evaluating X at x), then `resultant A B` evaluated at `x` is 0.
    Crucially, if `(quot_Y x).natDegree ≤ b_y - a_y` (bounded degree quotient), and `A(x, Y)` doesn't drop degree too much, then `x` is a root of `resultant A B` with multiplicity at least `a_y` (or `natDegreeY A`).
    Reference: Lemma 4.3 in Ben-Sasson et al. (2020) / Polishchuk-Spielman.

5.  **Contradiction via Counting**:
    Assume `resultant A B ≠ 0`.
    Summing the degrees:
    `n_x * a_y ≤ (resultant A B).natDegree` (by multiplicity)
    `n_x * a_y ≤ a_y * b_x + b_y * a_x`
    Similarly for the other direction (swapping X and Y):
    `n_y * a_x ≤ a_x * b_y + b_x * a_y`

    Combine these with the hypothesis `b_x/n_x + b_y/n_y < 1`.
    This should lead to a contradiction, implying `resultant A B = 0`.

6.  **Common Factor**:
    If `resultant A B = 0`, then `A` and `B` share a common factor `G` in `F[X][Y]`.
    Divide `A` and `B` by `G` to get `A', B'` with smaller degrees.
    Show that `A', B'` satisfy the same hypotheses (degree bounds, quotient existence).
    Use induction on the degree of `A` (or total degree) to conclude `A' | B'`, and thus `A | B`.

---
Proof from Ben-Sasson et al. (2020), Appendix D (Transcribed):

Mapping of notation:
Lean `x` <-> Paper `X`
Lean `y` <-> Paper `Z`
Lean `a_x` <-> Paper `aX`
Lean `a_y` <-> Paper `aZ`
Lean `b_x` <-> Paper `bX`
Lean `b_y` <-> Paper `bZ`
Lean `n_x` <-> Paper `nX`
Lean `n_y` <-> Paper `nZ`

"Clearly, we may assume B is not the zero polynomial (otherwise, the results are trivial). It then follows that A is also not the zero polynomial. We may also assume that either degX(A) = aX or degX(B) = bX. If not, then we may decrease aX and bX by 1 without changing dX = bX - aX or any other assumption (in particular, the LHS of (⋆) strictly decreases), and repeat until at least one equality holds. In fact, once we are done subtracting, we will necessarily have degX(A) = aX. Similarly, by reducing aZ and bZ if necessary, we may assume degZ(A) = aZ.

Next, let G(X, Z) ∈ F[X, Z] be the greatest common divisor of A and B; we aim to prove that G = A. Let gX = degX(G), gZ = degZ(G), and replace both A and B with the quotients A/G and B/G. The degrees and their bounds aX, bX decrease by exactly gX, and aZ, bZ decrease by gZ; it follows that dX, dZ are unchanged, and neither is the quotient B/A. The number of good substitutions nX also decreases by (at most) gX, and similarly nZ decreases by at most gZ. At most gX of the x ∈ F can satisfy G(x, Z) = 0, and in any of at least nX - gX good substitution with G(x, Z) ≠ 0, we can divide both sides of B(x, Z) = PZ,x(Z)A(x, Z) by G(x, Z) to obtain (B/G)(x, Z) = PZ,x(Z)(A/G)(x, Z). Since bX/nX < 1 and gX ≥ 0, we will have (bX - gX)/(nX - gX) ≤ bX/nX, and thus (bX - gX)/(nX - gX) + (bZ - gZ)/(nZ - gZ) ≤ bX/nX + bZ/nZ < 1, so assumption (⋆) still holds.

Additionally, A and B are now coprime. We will prove that in this case we must have aX = aZ = 0, i.e. A is a constant function. Let MX(Z) = SylX(A, B) be the Sylvester matrix of A and B in variable X. It is a square matrix of order aX + bX. Let RX(Z) = det MX(Z) be the determinant, which is not identically 0 since the polynomials are coprime. We have degZ(RX) ≤ aXbZ + aZbX. We denote D := aXbZ + aZbX.

For any of the nZ good values of z ∈ F, the fact that B(X, z) = PX,z(X)A(X, z) with degX(P) ≤ dX = bX - aX implies that each of the first aX rows of MX(z) is a linear combination of (at most) dX + 1 of the bX rows corresponding to coefficients of A(X, z). It follows that rk MX(z) ≤ bX, from which it follows that RX and its first aX - 1 derivatives vanish at Z = z, i.e. RX has a zero of multiplicity at least aX at every such z.

We have obtained that RX is a non-vanishing polynomial of degree at most D, with at least nZ roots of multiplicity aX each, thus aX * nZ ≤ D. Repeating the argument with the roles of X and Z switched, we find aZ * nX ≤ D as well. Thus:
D = aXbZ + aZbX = (bZ/nZ) * aXnZ + (bX/nX) * aZnX ≤ (bZ/nZ) * D + (bX/nX) * D = (bX/nX + bZ/nZ) * D.
However, (⋆) yields bX/nX + bZ/nZ < 1, so D must be 0. Since nX, nZ > 0, we must have aX = aZ = 0.

Thus A is a constant, so A | B, and P = B/A satisfies degX(P) = degX(B) ≤ bX = dX and degZ(P) ≤ dZ. For substitutions z, P(X, z)A(X, z) = B(X, z) = PX,z(X)A(X, z), so P(X, z) = PX,z(X) for almost all z."

---
Technical Hints & Formalization Notes:

1.  **Resultant Degree Bound (Crucial Step):**
    The step `degZ(RX) ≤ aXbZ + aZbX` is a property of the Resultant.
    If viewing `A, B ∈ F[Z][X]` (polynomials in X with coefficients in F[Z]), then `RX = resultant A B` is in `F[Z]`.
    The bound refers to the degree in Z.
    Since `resultant A B` is the determinant of the Sylvester matrix `Syl(A, B)`, and entries of `Syl(A, B)` are coefficients of `A` and `B` (in `F[Z]`), the degree bound follows from the definition of the determinant:
    `det(M) = ∑ σ(...) ∏ M_{i, σ(i)}`.
    The weights `aX` and `bX` (degrees in X) determine the size of the matrix (`aX + bX`).
    The degrees `aZ` and `bZ` (degrees in Z) determine the degree of entries.
    Specifically, the Sylvester matrix has `bX` rows of `A` coefficients (degree `≤ aZ`) and `aX` rows of `B` coefficients (degree `≤ bZ`).
    Thus `deg(det) ≤ bX * aZ + aX * bZ`.

2.  **Multiplicity & Hasse Derivatives:**
    The paper mentions "Hasse derivatives" to handle multiplicity in fields of finite characteristic.
    In `ArkLib`, `rootMultiplicity` (defined in `Data/Polynomial/Bivariate.lean`) is defined via shifting the polynomial `f.comp (Y + C (C y))` and looking at the valuation.
    These definitions are equivalent. The prover should use `rootMultiplicity` and `rootMultiplicity_some_implies_root` to show that if `resultant A B` has many roots of high multiplicity, it must be zero.

3.  **Linear Algebra / Rank Argument:**
    The proof states: "each of the first aX rows... is a linear combination of... the bX rows".
    This corresponds to the fact that if `B(x) = Q * A(x)` for some polynomial `Q`, then the rows of the Sylvester matrix corresponding to `B` are linearly dependent on the rows corresponding to `A` (evaluated at `x`).
    Specifically, the existence of a solution `(Q, -1)` to `A*Q - B*1 = 0` implies the kernel of the Sylvester matrix is non-trivial, effectively reducing its rank.
    This rank reduction implies the determinant (`resultant`) vanishes at `x`.

4.  **Handling Rational Inequalities:**
    The hypothesis `1 > (b_x : ℚ) / n_x + (b_y : ℚ) / n_y` uses rationals.
    The proof derives `D = ... ≤ (bZ/nZ + bX/nX) * D < D`.
    To formalize this in Lean (which might prefer `ℕ`), you can clear denominators:
    `n_x * n_y > b_x * n_y + b_y * n_x`.
    Then the contradiction becomes `D * n_x * n_y ≤ ... < D * n_x * n_y`.
-/
lemma Polishchuk_Spielman {F : Type} [Field F]
  (a_x a_y b_x b_y : ℕ) (n_x n_y : ℕ+)
  (h_bx_ge_ax : b_x ≥ a_x) (h_by_ge_ay : b_y ≥ a_y)
  (A B : F[X][Y])
  (h_f_degX : a_x ≥ Bivariate.degreeX A) (h_g_degX : b_x ≥ Bivariate.degreeX B)
  (h_f_degY : a_y ≥ natDegreeY A) (h_g_degY : b_y ≥ natDegreeY B)
  (P_x P_y : Finset F) [Nonempty P_x] [Nonempty P_y]
  (quot_X : F → F[X]) (quot_Y : F → F[X])
  (h_card_Px : n_x ≤ P_x.card) (h_card_Py : n_y ≤ P_y.card)
  (h_quot_X : ∀ y ∈ P_y,
    (quot_X y).natDegree ≤ (b_x - a_x) ∧ Bivariate.evalY y B = (quot_X y) * (Bivariate.evalY y A))
  (h_quot_Y : ∀ x ∈ P_x,
    (quot_Y x).natDegree ≤ (b_y - a_y) ∧ Bivariate.evalX x B = (quot_Y x) * (Bivariate.evalX x A))
  (h_le_1 : 1 > (b_x : ℚ) / (n_x : ℚ) + (b_y : ℚ) / (n_y : ℚ))
  : ∃ P : F[X][Y], B = P * A
    ∧ Bivariate.degreeX P ≤ b_x - a_x ∧ natDegreeY P ≤ b_y - a_y
    ∧ (∃ Q_x : Finset F, Q_x.card ≥ n_x - a_x ∧ Q_x ⊆ P_x ∧
        ∀ x ∈ Q_x, Bivariate.evalX x P = quot_Y x)
    ∧ (∃ Q_y : Finset F, Q_y.card ≥ n_y - a_y ∧ Q_y ⊆ P_y ∧
        ∀ y ∈ Q_y, Bivariate.evalY y P = quot_X y)
    := sorry
