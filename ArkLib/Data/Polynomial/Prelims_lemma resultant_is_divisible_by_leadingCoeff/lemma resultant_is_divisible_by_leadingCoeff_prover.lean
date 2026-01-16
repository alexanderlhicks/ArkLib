import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Order.Fin.Basic

theorem sylvester_last_row_castAdd {R : Type} [Semiring R] (f g : Polynomial R) (m n : ℕ) [NeZero (n + m)] (j : Fin n) :
  Polynomial.sylvester f g m n (⊤ : Fin (n + m)) (Fin.castAdd m j) =
    if (j : ℕ) = n - 1 then f.coeff m else 0 := by
  classical
  simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_top]
  by_cases hj : (j : ℕ) = n - 1
  ·
    have hnpos : 0 < n := Fin.size_positive j
    -- rewrite the goal using `hj` and prove the interval condition
    have hC : n ≤ n + m - 1 + 1 ∧ n + m ≤ n - 1 + m + 1 := by
      omega
    have hidx : n + m - 1 - (n - 1) = m := by
      omega
    simp [hj, hC, hidx]
  ·
    have hC : ¬((j : ℕ) ≤ n + m - 1 ∧ n + m ≤ (j : ℕ) + m + 1) := by
      intro h
      have : (j : ℕ) = n - 1 := by
        omega
      exact hj this
    simp [hj, hC]


theorem sylvester_last_row_natAdd {R : Type} [Semiring R] (f g : Polynomial R) (m n : ℕ) [NeZero (n + m)] (j : Fin m) :
  Polynomial.sylvester f g m n (⊤ : Fin (n + m)) (Fin.natAdd n j) =
    if (j : ℕ) = m - 1 then g.coeff n else 0 := by
  classical
  -- unfold sylvester and reduce the column case split
  simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_top]
  by_cases hj : (j : ℕ) = m - 1
  · -- `j` is the last element of `Fin m`
    have hmpos : 0 < m := Fin.size_positive j
    have h1le : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel h1le

    -- the (rewritten) inequality condition in the left `if` is true
    have hnmpos : 0 < n + m := Nat.pos_of_ne_zero (NeZero.ne (n + m))
    have hnm1le : 1 ≤ n + m := Nat.succ_le_of_lt hnmpos
    have hsub : n + m - 1 + 1 = n + m := Nat.sub_add_cancel hnm1le

    have hsum : m - 1 + n + 1 = n + m := by
      calc
        m - 1 + n + 1 = (m - 1) + (n + 1) := by
          simp [Nat.add_assoc]
        _ = (m - 1) + (1 + n) := by
          simp [Nat.add_comm]
        _ = (m - 1 + 1) + n := by
          simp [Nat.add_assoc]
        _ = m + n := by
          simp [hm1]
        _ = n + m := by
          simp [Nat.add_comm]

    have hC : m ≤ n + m - 1 + 1 ∧ n + m ≤ m - 1 + n + 1 := by
      constructor
      · -- `m ≤ n+m`
        have hmle : m ≤ n + m := by
          simpa [Nat.add_comm] using Nat.le_add_left m n
        simpa [hsub] using hmle
      · simpa [hsum] using (le_rfl : n + m ≤ n + m)

    -- simplify the coefficient index
    have hnm1 : n + m - 1 = n + (m - 1) := by
      -- move the subtraction inside the `m`
      simpa using (add_tsub_assoc_of_le (a := n) (b := m) (c := 1) h1le)
    have hidx : n + m - 1 - (m - 1) = n := by
      calc
        n + m - 1 - (m - 1) = (n + (m - 1)) - (m - 1) := by
          simp [hnm1]
        _ = n := by
          simpa using (add_tsub_cancel_right n (m - 1))

    simp [hj, hC, hidx]
  · -- `j` is not the last element
    have hmpos : 0 < m := Fin.size_positive j
    have h1le : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel h1le

    have hsum : m - 1 + n + 1 = n + m := by
      calc
        m - 1 + n + 1 = (m - 1) + (n + 1) := by
          simp [Nat.add_assoc]
        _ = (m - 1) + (1 + n) := by
          simp [Nat.add_comm]
        _ = (m - 1 + 1) + n := by
          simp [Nat.add_assoc]
        _ = m + n := by
          simp [hm1]
        _ = n + m := by
          simp [Nat.add_comm]

    have hcond_false : ¬((j : ℕ) ≤ n + m - 1 ∧ n + m ≤ (j : ℕ) + n + 1) := by
      intro hcond
      have hright := hcond.2
      -- rewrite the right inequality so we can cancel `n+1`
      have hright1 : n + m ≤ (j : ℕ) + (n + 1) := by
        simpa [Nat.add_assoc] using hright
      have hnm : n + m = (m - 1) + (n + 1) := by
        -- use `hsum` and regroup
        simpa [Nat.add_assoc] using hsum.symm
      have hright' : (m - 1) + (n + 1) ≤ (j : ℕ) + (n + 1) := by
        simpa [hnm] using hright1
      have hmlt : m - 1 ≤ (j : ℕ) := Nat.le_of_add_le_add_right hright'
      have hjle : (j : ℕ) ≤ m - 1 := Nat.le_pred_of_lt j.isLt
      have hjeq : (j : ℕ) = m - 1 := Nat.le_antisymm hjle hmlt
      exact hj hjeq

    simp [hj, hcond_false]


theorem sylvester_last_row {R : Type} [Semiring R] (f g : Polynomial R) (m n : ℕ) [NeZero (n + m)] :
  (Polynomial.sylvester f g m n (⊤ : Fin (n + m))) =
    fun j =>
      j.addCases
        (fun j₁ : Fin n => if (j₁ : ℕ) = n - 1 then f.coeff m else 0)
        (fun j₁ : Fin m => if (j₁ : ℕ) = m - 1 then g.coeff n else 0) := by
  classical
  funext j
  cases j using Fin.addCases with
  | left j₁ =>
      simpa using
        (sylvester_last_row_castAdd (f := f) (g := g) (m := m) (n := n) (j := j₁))
  | right j₁ =>
      simpa using
        (sylvester_last_row_natAdd (f := f) (g := g) (m := m) (n := n) (j := j₁))


theorem resultant_is_divisible_by_leadingCoeff {F : Type} [CommRing F] [Inhabited F] (f : Polynomial F) (hf : 0 < f.degree) :
  ∃ r',
    Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) =
      f.leadingCoeff * r' := by
  classical
  have hd : 0 < f.natDegree := (Polynomial.natDegree_pos_iff_degree_pos).2 hf
  let d : ℕ := f.natDegree
  let n : ℕ := d - 1
  let m : ℕ := d
  have hm : 0 < m := by
    simpa [m] using hd
  have hpos : 0 < n + m := by
    exact lt_of_lt_of_le hm (Nat.le_add_left m n)
  letI : NeZero (n + m) := ⟨Nat.ne_of_gt hpos⟩
  let A : Matrix (Fin (n + m)) (Fin (n + m)) F :=
    Polynomial.sylvester f f.derivative m n
  let i : Fin (n + m) := ⊤
  let u : Fin (n + m) → F := fun j =>
    j.addCases
      (fun j₁ : Fin n => if (j₁ : ℕ) = n - 1 then (1 : F) else 0)
      (fun j₁ : Fin m => if (j₁ : ℕ) = m - 1 then (d : F) else 0)
  have hmcoeff : f.coeff m = f.leadingCoeff := by
    simpa [m, d] using (Polynomial.coeff_natDegree f)
  have hnd : n + 1 = d := by
    have h1 : 1 ≤ d := Nat.succ_le_iff.2 hd
    simpa [n] using (Nat.sub_add_cancel h1)
  have hdercoeff : (f.derivative).coeff n = f.leadingCoeff * (d : F) := by
    have hcast' : ((n + 1 : ℕ) : F) = (d : F) :=
      congrArg (fun t : ℕ => (t : F)) hnd
    have hcast : (↑n + (1 : F)) = (d : F) := by
      simpa [Nat.cast_add, Nat.cast_one] using hcast'
    have hdcoeff : f.coeff d = f.leadingCoeff := by
      simpa [d] using (Polynomial.coeff_natDegree f)
    -- coefficient formula for derivative
    rw [Polynomial.coeff_derivative]
    -- rewrite n+1 = d in the coefficient
    rw [hnd]
    -- rewrite f.coeff d
    rw [hdcoeff]
    -- rewrite the scalar factor
    rw [hcast]
  have hrow : A i = f.leadingCoeff • u := by
    have hlast :
        A i =
          fun j =>
            j.addCases
              (fun j₁ : Fin n => if (j₁ : ℕ) = n - 1 then f.coeff m else 0)
              (fun j₁ : Fin m =>
                if (j₁ : ℕ) = m - 1 then (f.derivative).coeff n else 0) := by
      simpa [A, i] using
        (sylvester_last_row (R := F) (f := f) (g := f.derivative) (m := m) (n := n))
    ext j
    cases j using Fin.addCases with
    | left j₁ =>
        by_cases hj : (j₁ : ℕ) = n - 1
        · simp [hlast, u, hj, hmcoeff, smul_eq_mul]
        · simp [hlast, u, hj, smul_eq_mul]
    | right j₁ =>
        by_cases hj : (j₁ : ℕ) = m - 1
        · simp [hlast, u, hj, hdercoeff, smul_eq_mul]
        · simp [hlast, u, hj, smul_eq_mul]
  let N : Matrix (Fin (n + m)) (Fin (n + m)) F := A.updateRow i u
  refine ⟨N.det, ?_⟩
  have hA : A.updateRow i (A i) = A := by
    simpa using (Matrix.updateRow_eq_self (A := A) i)
  calc
    Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) = A.det := by
      simp [Polynomial.resultant, A, d, n, m]
    _ = (A.updateRow i (A i)).det := by
      simp [hA]
    _ = (A.updateRow i (f.leadingCoeff • u)).det := by
      simp [hrow]
    _ = f.leadingCoeff * (A.updateRow i u).det := by
      simp [Matrix.det_updateRow_smul]
    _ = f.leadingCoeff * N.det := by
      simp [N]


