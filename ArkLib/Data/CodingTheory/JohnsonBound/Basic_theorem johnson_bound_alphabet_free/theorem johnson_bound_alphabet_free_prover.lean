import Mathlib
import ArkLib.Data.CodingTheory.Basic
import Mathlib.InformationTheory.Hamming
import ArkLib.Data.CodingTheory.JohnsonBound.Expectations
import Mathlib.Data.Real.Sqrt
import ArkLib.Data.CodingTheory.JohnsonBound.Basic

open scoped BigOperators

theorem johnson_bound_alphabet_free_ball_rat_eq {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {v : Fin n → F} {e : ℕ} :
  ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _) =
    ({ x : (Fin n → F) | (Δ₀(x, v) : ℚ) ≤ (e : ℚ) } : Finset _) := by
  ext x
  simp [Nat.cast_le]

theorem johnson_bound_alphabet_free_ball_subset {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ} :
  B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _) ⊆ B := by
  intro x hx
  exact (Finset.mem_inter.mp hx).1


noncomputable def johnson_bound_alphabet_free_dmin {n : ℕ} {F : Type*} [DecidableEq F]
  (B : Finset (Fin n → F)) : ℕ :=
  sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }

theorem johnson_bound_alphabet_free_dmin_self {n : ℕ} {F : Type*} [DecidableEq F]
  (B : Finset (Fin n → F)) :
  johnson_bound_alphabet_free_dmin (n := n) (F := F) B = johnson_bound_alphabet_free_dmin (n := n) (F := F) B :=   rfl


theorem johnson_bound_alphabet_free_eAvg_le_e [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ} {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ}
  (hpos : (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)).card > 0) :
  JohnsonBound.e (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)) v ≤ (e : ℚ) := by
  classical
  -- Rewrite the integer-radius ball into a rational-radius ball.
  have hpos' := hpos
  rw [johnson_bound_alphabet_free_ball_rat_eq (v := v) (e := e)] at hpos'
  -- Now apply the generic bound on the expectation over a ball of radius `r = e`.
  have h :=
    JohnsonBound.e_ball_le_radius (B := B) v (e : ℚ) (by
      simpa using hpos')
  -- Rewrite back to the original (ℕ-radius) ball.
  simpa [johnson_bound_alphabet_free_ball_rat_eq (v := v) (e := e)] using h

theorem johnson_bound_alphabet_free_e_div_n_le_one {n e : ℕ} (hn : 0 < n) (he : e < n) : ((e : ℚ) / n) ≤ 1 := by
  have hnq : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast hn
  have heq : (e : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast (Nat.le_of_lt he)
  -- use div_le_one with positive denominator
  exact (div_le_one hnq).2 heq


theorem johnson_bound_alphabet_free_field_card_pos [Field F] [Fintype F] : (0 : ℕ) < Fintype.card F := by
  classical
  haveI : Nonempty F := ⟨0⟩
  exact Fintype.card_pos

theorem johnson_bound_alphabet_free_gap_pos_rat {n d e : ℕ} (hn : 0 < n)
  (hgap : (0 : ℤ) < (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ)^2) :
  (0 : ℚ) < (d : ℚ) / n - 2 * (e : ℚ) / n + ((e : ℚ) / n)^2 := by
  classical
  let g : ℤ := (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ) ^ 2
  have hg0 : (0 : ℚ) < (g : ℚ) := by
    have : (0 : ℚ) < ((↑n : ℤ) * d - 2 * (↑n : ℤ) * e + (↑e : ℤ) ^ 2 : ℚ) := by
      exact_mod_cast hgap
    simpa [g] using this
  have hnq : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast hn
  have hnq0 : (n : ℚ) ≠ 0 := by
    exact ne_of_gt hnq
  have hnq2 : (0 : ℚ) < (n : ℚ) ^ 2 := by
    simpa [pow_two] using mul_pos hnq hnq
  have hrewrite : (d : ℚ) / n - 2 * (e : ℚ) / n + ((e : ℚ) / n) ^ 2 = (g : ℚ) / (n : ℚ) ^ 2 := by
    -- clear denominators
    field_simp [hnq0]
    -- unfold g and simplify
    simp [g]
    ring
  -- conclude
  have : (0 : ℚ) < (g : ℚ) / (n : ℚ) ^ 2 := by
    exact div_pos hg0 hnq2
  simpa [hrewrite] using this

theorem johnson_bound_alphabet_free_list_trivial [Field F] [Fintype F]
  {n d : ℕ} {L : ℕ}
  (hqn : 0 < (Fintype.card F : ℚ) * d * n)
  (hL : L ≤ 1) :
  (L : ℚ) ≤ (Fintype.card F : ℚ) * d * n := by
  classical
  have hLq : (L : ℚ) ≤ (1 : ℚ) := by
    exact_mod_cast hL
  have hnat : 0 < Fintype.card F * d * n := by
    -- convert hqn to a statement about naturals
    exact_mod_cast hqn
  have hR : (1 : ℚ) ≤ (Fintype.card F : ℚ) * d * n := by
    -- RHS is a positive integer, hence at least 1
    have h1nat : 1 ≤ Fintype.card F * d * n := by
      exact Nat.succ_le_iff.2 hnat
    -- cast back to ℚ
    exact_mod_cast h1nat
  linarith

theorem johnson_bound_alphabet_free_mindist_subset {n : ℕ} {F : Type*} [DecidableEq F]
  {B S : Finset (Fin n → F)}
  (hSB : S ⊆ B)
  (hS : 1 < S.card) :
  let dB : ℕ := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let dS : ℕ := sInf { d | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ hammingDist u v = d }
  dB ≤ dS := by
  classical
  dsimp
  have hdist :
      { d | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ hammingDist u v = d }
        ⊆ { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d } := by
    intro d hd
    rcases hd with ⟨u, huS, v, hvS, huv, hUv⟩
    exact ⟨u, hSB huS, v, hSB hvS, huv, hUv⟩
  have hDSne :
      ({ d | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ hammingDist u v = d } : Set ℕ).Nonempty := by
    rcases (Finset.one_lt_card.mp hS) with ⟨u, huS, v, hvS, huv⟩
    refine ⟨hammingDist u v, ?_⟩
    exact ⟨u, huS, v, hvS, huv, rfl⟩
  have hm :
      sInf ({ d | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ hammingDist u v = d } : Set ℕ)
        ∈ { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d } := by
    exact hdist (Nat.sInf_mem hDSne)
  exact Nat.sInf_le hm


theorem johnson_bound_alphabet_free_minDist_ball_ge {n : ℕ} {F : Type*} [Fintype F] [DecidableEq F]
  {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ}
  (hB2 : 1 < (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)).card) :
  let dB : ℕ := sInf { d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d }
  let dB2 : ℕ := sInf { d | ∃ u ∈ (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)),
                        ∃ v' ∈ (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)),
                        u ≠ v' ∧ hammingDist u v' = d }
  dB ≤ dB2 := by
  classical
  simpa using
    (johnson_bound_alphabet_free_mindist_subset
      (B := B)
      (S := B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _))
      (johnson_bound_alphabet_free_ball_subset (B := B) (v := v) (e := e))
      hB2)

theorem johnson_bound_alphabet_free_d_le_davg_ball [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ} {B : Finset (Fin n → F)} {v : Fin n → F} {e d : ℕ}
  {B2 : Finset (Fin n → F)}
  (hB2 : B2 = B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _))
  (hdmin : d = sInf { d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d })
  (hcard : 1 < B2.card) :
  ((d : ℚ) ≤ JohnsonBound.d B2) := by
  classical
  have hB2' : 1 < (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)).card := by
    simpa [hB2] using hcard

  have hminNat :
      sInf { d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d } ≤
        sInf { d |
          ∃ u ∈ (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)),
            ∃ v' ∈ (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)),
              u ≠ v' ∧ hammingDist u v' = d } := by
    simpa using
      (johnson_bound_alphabet_free_minDist_ball_ge (n := n) (F := F) (B := B) (v := v) (e := e) hB2')

  have hdleInter :
      d ≤
        sInf { d |
          ∃ u ∈ (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)),
            ∃ v' ∈ (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)),
              u ≠ v' ∧ hammingDist u v' = d } := by
    simpa [← hdmin] using hminNat

  have hdleB2 : d ≤ sInf { d | ∃ u ∈ B2, ∃ v' ∈ B2, u ≠ v' ∧ hammingDist u v' = d } := by
    -- rewrite the goal using the definition of `B2`
    simpa [hB2] using hdleInter

  have hminB2 :
      sInf { d | ∃ u ∈ B2, ∃ v' ∈ B2, u ≠ v' ∧ hammingDist u v' = d } ≤
        JohnsonBound.d B2 := by
    simpa using (JohnsonBound.min_dist_le_d (B := B2) (F := F) (n := n) (h_B := hcard))

  have hdleQ :
      (d : ℚ) ≤
        sInf { d | ∃ u ∈ B2, ∃ v' ∈ B2, u ≠ v' ∧ hammingDist u v' = d } := by
    exact_mod_cast hdleB2

  exact le_trans hdleQ hminB2

theorem johnson_bound_alphabet_free_n_pos {n d e : ℕ} :
  (e : ℝ) < (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ) → 0 < n := by
  intro h
  have hn : n ≠ 0 := by
    intro hn0
    subst hn0
    have hlt : (e : ℝ) < 0 := by
      simpa using h
    exact (not_lt_of_ge (Nat.cast_nonneg e)) hlt
  exact Nat.pos_of_ne_zero hn


theorem johnson_bound_alphabet_free_condition_to_integral_gap {n d e : ℕ} :
  (e : ℝ) < (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ)
  → (0 : ℤ) < (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ)^2 := by
  intro h
  have hsqrt : Real.sqrt ((n * (n - d) : ℕ) : ℝ) < (n : ℝ) - e := by
    linarith
  have hpos : 0 < (n : ℝ) - e := by
    have h0 : (0 : ℝ) ≤ Real.sqrt ((n * (n - d) : ℕ) : ℝ) := by
      exact Real.sqrt_nonneg _
    exact lt_of_le_of_lt h0 hsqrt
  have hsq : ((n * (n - d) : ℕ) : ℝ) < ((n : ℝ) - e) ^ 2 := by
    exact (Real.sqrt_lt' hpos).1 hsqrt
  -- extract e < n, needed in second case
  have hen : (e : ℝ) < (n : ℝ) := by
    have h0 : (0 : ℝ) ≤ Real.sqrt ((n * (n - d) : ℕ) : ℝ) := by
      exact Real.sqrt_nonneg _
    have hnle : (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact sub_le_self _ h0
    exact lt_of_lt_of_le h hnle
  -- split on d ≤ n
  rcases le_total d n with hdn | hnd
  · -- case d ≤ n
    have hR : (0 : ℝ) < (n : ℝ) * d - 2 * (n : ℝ) * e + (e : ℝ) ^ 2 := by
      -- rewrite the left side of hsq using hdn
      have hsq' : (n : ℝ) * ((n : ℝ) - d) < ((n : ℝ) - e) ^ 2 := by
        -- convert hsq
        simpa [Nat.cast_mul, Nat.cast_sub hdn, mul_sub] using hsq
      -- now expand squares and finish
      nlinarith [hsq']
    -- cast back to ℤ
    have hZ : (0 : ℝ) < (( (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ) ^ 2) : ℝ) := by
      -- same as hR, but with ℤ expression
      simpa [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hR
    exact_mod_cast hZ
  · -- case n ≤ d
    have hnd0 : n - d = 0 := by
      exact tsub_eq_zero_of_le hnd
    -- use e < n to show n - e ≠ 0
    have hne0 : (n : ℝ) - e ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) - e := by
        -- from hen
        linarith
      exact ne_of_gt this
    have hR : (0 : ℝ) < (n : ℝ) * d - 2 * (n : ℝ) * e + (e : ℝ) ^ 2 := by
      -- expression equals (n-e)^2 + n*(d-n)
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (johnson_bound_alphabet_free_n_pos (n:=n) (d:=d) (e:=e) h)
      have hdpos : (0 : ℝ) ≤ (d : ℝ) - n := by
        exact sub_nonneg.mpr (by exact_mod_cast hnd)
      have hterm : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) - n) := by
        exact mul_nonneg (le_of_lt hnpos) hdpos
      have hsquare : (0 : ℝ) < ((n : ℝ) - e) ^ 2 := by
        -- square positive since n-e ≠ 0
        exact (sq_pos_iff).2 hne0
      -- now show
      nlinarith [hsquare, hterm]
    have hZ : (0 : ℝ) < (((n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ) ^ 2 : ℤ) : ℝ) := by
      simpa [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hR
    exact_mod_cast hZ

theorem johnson_bound_alphabet_free_e_lt_n {n d e : ℕ} :
  (e : ℝ) < (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ)
  → e < n := by
  intro h
  have hsqrt : (0 : ℝ) ≤ Real.sqrt ((n * (n - d) : ℕ) : ℝ) := by
    exact Real.sqrt_nonneg _
  have hle : (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact sub_le_self _ hsqrt
  have hlt : (e : ℝ) < (n : ℝ) := lt_of_lt_of_le h hle
  exact_mod_cast hlt


def johnson_bound_alphabet_free_q (F : Type*) [Fintype F] : ℚ := (Fintype.card F : ℚ)

def johnson_bound_alphabet_free_frac (F : Type*) [Fintype F] : ℚ :=
  let q : ℚ := (Fintype.card F : ℚ)
  q / (q - 1)

theorem johnson_bound_alphabet_free_frac_def (F : Type*) [Fintype F] :
  johnson_bound_alphabet_free_frac F =
    ((Fintype.card F : ℚ) / ((Fintype.card F : ℚ) - 1)) := by
  simp [johnson_bound_alphabet_free_frac]

theorem johnson_bound_alphabet_free_frac_pos [Field F] [Fintype F] : 0 < johnson_bound_alphabet_free_frac F := by
  classical
  dsimp [johnson_bound_alphabet_free_frac]
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hq : (1 : ℚ) < (Fintype.card F : ℚ) := by
    exact_mod_cast hcard
  have hnum : (0 : ℚ) < (Fintype.card F : ℚ) := lt_trans (by norm_num) hq
  have hden : (0 : ℚ) < (Fintype.card F : ℚ) - 1 := sub_pos.2 hq
  exact div_pos hnum hden

theorem johnson_bound_alphabet_free_one_le_frac [Field F] [Fintype F] : (1 : ℚ) ≤ johnson_bound_alphabet_free_frac F := by
  classical
  -- Unfold the definition of the fraction
  simp [johnson_bound_alphabet_free_frac]
  -- Set q = |F| as a rational number
  set q : ℚ := (Fintype.card F : ℚ)
  have hq : (1 : ℚ) < q := by
    -- |F| > 1 since a field is nontrivial
    have hnat : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
    -- cast to ℚ
    simpa [q] using (show (1 : ℚ) < (Fintype.card F : ℚ) from by
      exact_mod_cast hnat)
  have hden : (0 : ℚ) < q - 1 := by linarith
  -- `1 ≤ q/(q-1)` is equivalent to `q-1 ≤ q` when `q-1 > 0`.
  exact (one_le_div hden).2 (by linarith)


theorem johnson_bound_alphabet_free_johnson_lemma_alphabet_free_form [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ} {B : Finset (Fin n → F)} {v : Fin n → F}
  (hn : 0 < n) (hB : 2 ≤ B.card) (hF : 2 ≤ Fintype.card F) :
  ((B.card : ℚ) * ((JohnsonBound.d B / n)
    - 2 * (JohnsonBound.e B v / n)
    + (JohnsonBound.e B v / n)^2))
    ≤ (JohnsonBound.d B / n) := by
  classical
  set denom : ℚ := (Fintype.card F - 1)
  set frac : ℚ := (Fintype.card F : ℚ) / denom
  set x : ℚ := JohnsonBound.e B v / n
  set y : ℚ := JohnsonBound.d B / n

  have hj : (B.card : ℚ) * ((1 - frac * x) ^ 2 - (1 - frac * y)) ≤ frac * y := by
    -- `johnson_bound_lemma` has the RHS as `frac * d / n`; rewrite it as `frac * (d / n)`
    simpa [denom, frac, x, y, mul_div_assoc] using
      (JohnsonBound.johnson_bound_lemma (B := B) (v := v) hn hB hF)

  have hdenom_pos : (0 : ℚ) < denom := by
    -- `hF : 2 ≤ card F` implies `0 < card F - 1`
    have : 0 < Fintype.card F - 1 := by omega
    -- cast to ℚ
    have : (0 : ℚ) < ((Fintype.card F - 1 : ℕ) : ℚ) := by
      exact_mod_cast this
    simpa [denom] using this

  have hnum_pos : (0 : ℚ) < (Fintype.card F : ℚ) := by
    exact_mod_cast (by omega : (0 : ℕ) < Fintype.card F)

  have hfrac_pos : 0 < frac := by
    -- `frac = card/denom`
    have : 0 < (Fintype.card F : ℚ) / denom := by
      exact div_pos hnum_pos hdenom_pos
    simpa [frac] using this

  have hfrac_ge : (1 : ℚ) ≤ frac := by
    have hle_nat : Fintype.card F - 1 ≤ Fintype.card F := by
      exact Nat.sub_le _ _
    have hle : denom ≤ (Fintype.card F : ℚ) := by
      have : ((Fintype.card F - 1 : ℕ) : ℚ) ≤ (Fintype.card F : ℚ) := by
        exact_mod_cast hle_nat
      simpa [denom] using this
    have : (1 : ℚ) ≤ (Fintype.card F : ℚ) / denom := (one_le_div hdenom_pos).2 hle
    simpa [frac] using this

  have h_expand : ((1 - frac * x) ^ 2 - (1 - frac * y)) = frac * (y - 2 * x + frac * x ^ 2) := by
    ring

  have hj' : frac * ((B.card : ℚ) * (y - 2 * x + frac * x ^ 2)) ≤ frac * y := by
    -- rewrite the Johnson lemma using the expansion
    have : (B.card : ℚ) * (frac * (y - 2 * x + frac * x ^ 2)) ≤ frac * y := by
      simpa [h_expand, mul_assoc] using hj
    -- commute to factor `frac` on the left
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  have hj_cancel : (B.card : ℚ) * (y - 2 * x + frac * x ^ 2) ≤ y := by
    exact le_of_mul_le_mul_left hj' hfrac_pos

  have hx2_nonneg : 0 ≤ x ^ 2 := by
    exact sq_nonneg x

  have h_mulx2 : x ^ 2 ≤ frac * x ^ 2 := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hfrac_ge hx2_nonneg)

  have h_inside : y - 2 * x + x ^ 2 ≤ y - 2 * x + frac * x ^ 2 := by
    simpa using (add_le_add_left h_mulx2 (y - 2 * x))

  have hBnonneg : 0 ≤ (B.card : ℚ) := by
    exact_mod_cast (Nat.zero_le B.card)

  have h_mul : (B.card : ℚ) * (y - 2 * x + x ^ 2) ≤ (B.card : ℚ) * (y - 2 * x + frac * x ^ 2) := by
    exact mul_le_mul_of_nonneg_left h_inside hBnonneg

  have : (B.card : ℚ) * (y - 2 * x + x ^ 2) ≤ y := le_trans h_mul hj_cancel

  -- unfold `x` and `y` back to match the goal
  simpa [x, y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

theorem johnson_bound_alphabet_free_quad_mono {x E : ℚ} (hE : x ≤ E) (hE1 : E ≤ 1) :
  x^2 - 2*x ≥ E^2 - 2*E := by
  have h1 : x - E ≤ 0 := by linarith
  have h2 : x + E - 2 ≤ 0 := by
    linarith [hE, hE1]
  have hprod : 0 ≤ (x - E) * (x + E - 2) := by
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hfactor : (x ^ 2 - 2 * x) - (E ^ 2 - 2 * E) = (x - E) * (x + E - 2) := by
    ring
  have hdiff : 0 ≤ (x ^ 2 - 2 * x) - (E ^ 2 - 2 * E) := by
    simpa [hfactor] using hprod
  exact (sub_nonneg).1 hdiff

theorem johnson_bound_alphabet_free_finish_from_hineq_stronger [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ} {B : Finset (Fin n → F)} {v : Fin n → F} {e d : ℕ}
  {B2 : Finset (Fin n → F)}
  (hB2 : B2 = B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _))
  (hn : 0 < n)
  (he : e < n)
  (hdmin : d = sInf { d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d })
  (hcard : 1 < B2.card)
  (hgap : (0 : ℤ) < (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ)^2)
  (hineq : ((B2.card : ℚ) * ((JohnsonBound.d B2 / n) - 2 * (JohnsonBound.e B2 v / n) + (JohnsonBound.e B2 v / n)^2))
            ≤ (JohnsonBound.d B2 / n)) :
  ((B2.card : ℚ) ≤ (d : ℚ) * n) := by
  classical
  -- Abbreviations
  let L : ℚ := (B2.card : ℚ)
  let x : ℚ := JohnsonBound.e B2 v / n
  let y : ℚ := JohnsonBound.d B2 / n
  let E : ℚ := (e : ℚ) / n
  let c : ℚ := E ^ 2 - 2 * E
  let den : ℚ := y - 2 * x + x ^ 2

  have hnq : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast hn
  have hnq' : (0 : ℚ) ≤ (n : ℚ) := le_of_lt hnq

  -- Step 1: bounds on y and x
  have hdle : (d : ℚ) ≤ JohnsonBound.d B2 :=
    johnson_bound_alphabet_free_d_le_davg_ball (F := F) (B := B) (v := v) (e := e) (d := d)
      (B2 := B2) hB2 hdmin hcard

  have hyd : (d : ℚ) / n ≤ y := by
    dsimp [y]
    have := div_le_div_of_nonneg_right hdle hnq'
    simpa using this

  -- positivity needed for eAvg lemma
  have hposInt : (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)).card > 0 := by
    have hposB2 : 0 < B2.card := lt_trans Nat.zero_lt_one hcard
    simpa [hB2] using hposB2

  have hEle : JohnsonBound.e B2 v ≤ (e : ℚ) := by
    have htmp :
        JohnsonBound.e (B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _)) v ≤ (e : ℚ) :=
      johnson_bound_alphabet_free_eAvg_le_e (F := F) (B := B) (v := v) (e := e) hposInt
    simpa [hB2] using htmp

  have hx : x ≤ E := by
    dsimp [x, E]
    have := div_le_div_of_nonneg_right hEle hnq'
    simpa using this

  have hE1 : E ≤ 1 := by
    dsimp [E]
    simpa using johnson_bound_alphabet_free_e_div_n_le_one (n := n) (e := e) hn he

  -- Step 2: quadratic comparison
  have hquad : c ≤ x ^ 2 - 2 * x := by
    have := johnson_bound_alphabet_free_quad_mono (x := x) (E := E) hx hE1
    -- unfold c
    dsimp [c] at *
    simpa using this

  have hden_ge : y + c ≤ den := by
    have h1 : y + c ≤ y + (x ^ 2 - 2 * x) := add_le_add_left hquad y
    have hden_eq : y + (x ^ 2 - 2 * x) = den := by
      dsimp [den]
      ring
    simpa [hden_eq] using h1

  -- Step 3: denominator positivity
  have hgaprat : (0 : ℚ) < (d : ℚ) / n + c := by
    have h0 := johnson_bound_alphabet_free_gap_pos_rat (n := n) (d := d) (e := e) hn hgap
    -- rewrite into the same shape
    have hEq :
        (d : ℚ) / n - 2 * (e : ℚ) / n + ((e : ℚ) / n) ^ 2 = (d : ℚ) / n + c := by
      dsimp [c, E]
      ring
    simpa [hEq] using h0

  have hyc_pos : (0 : ℚ) < y + c := by
    have hle : (d : ℚ) / n + c ≤ y + c := add_le_add_right hyd c
    exact lt_of_lt_of_le hgaprat hle

  have hden_pos : (0 : ℚ) < den := lt_of_lt_of_le hyc_pos hden_ge

  -- Step 4: divide hineq by positive denominator
  have hineq' : L * den ≤ y := by
    simpa [L, den, x, y] using hineq

  have hL_le_y_div_den : L ≤ y / den := by
    exact (le_div_iff₀ hden_pos).2 hineq'

  -- compare denominators: y/den ≤ y/(y+c)
  have hy0 : (0 : ℚ) ≤ y := by
    have hd0 : (0 : ℚ) ≤ (d : ℚ) / n := by
      have hd0' : (0 : ℚ) ≤ (d : ℚ) := by
        exact_mod_cast (Nat.zero_le d)
      exact div_nonneg hd0' hnq'
    exact le_trans hd0 hyd

  have hy_div_le : y / den ≤ y / (y + c) := by
    exact div_le_div_of_nonneg_left hy0 hyc_pos hden_ge

  -- Step 5: replace y by d/n using c ≤ 0
  have hE0 : (0 : ℚ) ≤ E := by
    dsimp [E]
    have he0 : (0 : ℚ) ≤ (e : ℚ) := by
      exact_mod_cast (Nat.zero_le e)
    exact div_nonneg he0 hnq'

  have hc_nonpos : c ≤ 0 := by
    -- c = E^2 - 2E = E*(E-2)
    have hE2 : E - 2 ≤ 0 := by linarith
    have hmul : E * (E - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hE0 hE2
    have hEq : c = E * (E - 2) := by
      dsimp [c]
      ring
    simpa [hEq] using hmul

  have hstep5 : y / (y + c) ≤ ((d : ℚ) / n) / ((d : ℚ) / n + c) := by
    -- use div_le_div_iff₀
    have hmul : y * ((d : ℚ) / n + c) ≤ ((d : ℚ) / n) * (y + c) := by
      have hyc : y * c ≤ ((d : ℚ) / n) * c := by
        have := mul_le_mul_of_nonpos_right hyd hc_nonpos
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      calc
        y * ((d : ℚ) / n + c) = y * ((d : ℚ) / n) + y * c := by ring
        _ ≤ y * ((d : ℚ) / n) + ((d : ℚ) / n) * c := by
          exact add_le_add_left hyc (y * ((d : ℚ) / n))
        _ = ((d : ℚ) / n) * y + ((d : ℚ) / n) * c := by ring
        _ = ((d : ℚ) / n) * (y + c) := by ring

    have hd0c_pos : (0 : ℚ) < (d : ℚ) / n + c := hgaprat
    exact (div_le_div_iff₀ hyc_pos hd0c_pos).2 hmul

  -- Step 6: compute and bound the last fraction
  let g : ℤ := (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ) ^ 2
  have hg_pos : (0 : ℤ) < g := by
    simpa [g] using hgap
  have hg1 : (1 : ℚ) ≤ (g : ℚ) := by
    simpa using (Int.cast_one_le_of_pos (R := ℚ) hg_pos)

  have hfrac_eq : ((d : ℚ) / n) / ((d : ℚ) / n + c) = (d : ℚ) * n / (g : ℚ) := by
    have hnq0 : (n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hg0 : (g : ℚ) ≠ 0 := by
      have : (g : ℤ) ≠ 0 := ne_of_gt hg_pos
      exact_mod_cast this
    have hdenEq : (d : ℚ) / n + c = (g : ℚ) / ((n : ℚ) ^ 2) := by
      dsimp [c, E, g]
      field_simp [hnq0]
      ring
    --
    rw [hdenEq]
    field_simp [hnq0, hg0]
    ring

  have hfinal_bound : ((d : ℚ) / n) / ((d : ℚ) / n + c) ≤ (d : ℚ) * n := by
    have hd0 : (0 : ℚ) ≤ (d : ℚ) := by
      exact_mod_cast (Nat.zero_le d)
    have hdnn : (0 : ℚ) ≤ (d : ℚ) * n := by
      exact mul_nonneg hd0 hnq'
    simpa [hfrac_eq] using (div_le_self hdnn hg1)

  -- Combine everything
  have hfinal : L ≤ (d : ℚ) * n := by
    exact le_trans hL_le_y_div_den (le_trans hy_div_le (le_trans hstep5 hfinal_bound))

  simpa [L] using hfinal

theorem johnson_bound_alphabet_free_two_le_field_card [Field F] [Fintype F] : 2 ≤ Fintype.card F := by
  classical
  have h : 1 < Fintype.card F := by
    simpa using (Fintype.one_lt_card (α := F))
  omega

theorem johnson_bound_alphabet_free_finish_from_hineq [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ} {B : Finset (Fin n → F)} {v : Fin n → F} {e d : ℕ}
  {B2 : Finset (Fin n → F)}
  (hB2 : B2 = B ∩ ({ x : (Fin n → F) | Δ₀(x, v) ≤ e } : Finset _))
  (hn : 0 < n)
  (he : e < n)
  (hdmin : d = sInf { d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d })
  (hcard : 1 < B2.card)
  (hgap : (0 : ℤ) < (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ)^2)
  (hineq : ((B2.card : ℚ) * ((JohnsonBound.d B2 / n) - 2 * (JohnsonBound.e B2 v / n) + (JohnsonBound.e B2 v / n)^2))
            ≤ (JohnsonBound.d B2 / n)) :
  ((B2.card : ℚ) ≤ (Fintype.card F : ℚ) * d * n) := by
  classical
  have hstrong : (B2.card : ℚ) ≤ (d : ℚ) * n :=
    johnson_bound_alphabet_free_finish_from_hineq_stronger
      (F := F) (n := n) (B := B) (v := v) (e := e) (d := d) (B2 := B2)
      hB2 hn he hdmin hcard hgap hineq

  have hq_nat : (1 : ℕ) ≤ Fintype.card F := by
    have h2 : (2 : ℕ) ≤ Fintype.card F :=
      johnson_bound_alphabet_free_two_le_field_card (F := F)
    exact le_trans (by decide : (1 : ℕ) ≤ 2) h2

  have hq : (1 : ℚ) ≤ (Fintype.card F : ℚ) := by
    exact_mod_cast hq_nat

  have hnonneg : (0 : ℚ) ≤ (d : ℚ) * n := by
    have hd0 : (0 : ℚ) ≤ (d : ℚ) := by
      exact_mod_cast (Nat.zero_le d)
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast (Nat.zero_le n)
    exact mul_nonneg hd0 hn0

  have hmul : (d : ℚ) * n ≤ (Fintype.card F : ℚ) * d * n := by
    calc
      (d : ℚ) * n = (1 : ℚ) * ((d : ℚ) * n) := by simp
      _ ≤ (Fintype.card F : ℚ) * ((d : ℚ) * n) := by
        exact mul_le_mul_of_nonneg_right hq hnonneg
      _ = (Fintype.card F : ℚ) * d * n := by
        ring

  exact le_trans hstrong hmul

theorem johnson_bound_alphabet_free [Field F] [Fintype F] [DecidableEq F]
  {n : ℕ}
  {B : Finset (Fin n → F)}
  {v : Fin n → F}
  {e : ℕ} :
  let d : ℕ := sInf { d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d }
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (e : ℝ) < (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ)
  →
  ((B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card : ℚ) ≤ q * d * n := by
  classical
  dsimp
  intro h
  set d : ℕ := sInf {d | ∃ u ∈ B, ∃ v' ∈ B, u ≠ v' ∧ hammingDist u v' = d} with hd
  set q : ℚ := (Fintype.card F : ℚ) with hq
  set B2 : Finset (Fin n → F) := B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _) with hB2
  by_cases hcard : B2.card ≤ 1
  ·
    have hn : 0 < n := by
      apply johnson_bound_alphabet_free_n_pos (n := n) (d := d) (e := e)
      simpa [hd] using h
    have hqpos : (0 : ℕ) < Fintype.card F := by
      simpa using (johnson_bound_alphabet_free_field_card_pos (F := F))
    have hdpos : 0 < d := by
      by_contra hd0
      have hd0' : d = 0 := by omega
      have h' : (e : ℝ) < (n : ℝ) - Real.sqrt ((n * (n - d) : ℕ) : ℝ) := by
        simpa [hd] using h
      have h'' : (e : ℝ) < (n : ℝ) - Real.sqrt ((n * (n - 0) : ℕ) : ℝ) := by
        simpa [hd0'] using h'
      have hsqrt : Real.sqrt ((n * (n - 0) : ℕ) : ℝ) = (n : ℝ) := by
        have : (n * (n - 0) : ℕ) = n * n := by simp
        simp [this]
      have : (e : ℝ) < 0 := by
        simpa [hsqrt] using h''
      have hnonneg : (0 : ℝ) ≤ e := by
        exact_mod_cast (Nat.zero_le e)
      exact (not_lt_of_ge hnonneg this)
    have hqn : 0 < (Fintype.card F : ℚ) * d * n := by
      have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
      have hdq : 0 < (d : ℚ) := by exact_mod_cast hdpos
      have hqq : 0 < (Fintype.card F : ℚ) := by exact_mod_cast hqpos
      have hqd : 0 < (Fintype.card F : ℚ) * (d : ℚ) := mul_pos hqq hdq
      have : 0 < ((Fintype.card F : ℚ) * (d : ℚ)) * (n : ℚ) := mul_pos hqd hnq
      simpa [mul_assoc] using this
    have htriv :=
      johnson_bound_alphabet_free_list_trivial (F := F) (n := n) (d := d) (L := B2.card) hqn hcard
    simpa [hB2, hq] using htriv
  ·
    have hcard' : 1 < B2.card := by omega
    have hn : 0 < n := by
      apply johnson_bound_alphabet_free_n_pos (n := n) (d := d) (e := e)
      simpa [hd] using h
    have he : e < n := by
      apply johnson_bound_alphabet_free_e_lt_n (n := n) (d := d) (e := e)
      simpa [hd] using h
    have hF2 : 2 ≤ Fintype.card F := by
      simpa using (johnson_bound_alphabet_free_two_le_field_card (F := F))
    have hB2' : 2 ≤ B2.card := by omega
    have hineq :=
      johnson_bound_alphabet_free_johnson_lemma_alphabet_free_form (F := F) (n := n) (B := B2)
        (v := v) hn hB2' hF2
    have hgap : (0 : ℤ) < (n : ℤ) * d - 2 * (n : ℤ) * e + (e : ℤ) ^ 2 := by
      apply johnson_bound_alphabet_free_condition_to_integral_gap (n := n) (d := d) (e := e)
      simpa [hd] using h
    have hfinish : ((B2.card : ℚ) ≤ (Fintype.card F : ℚ) * d * n) := by
      refine
        johnson_bound_alphabet_free_finish_from_hineq (F := F) (n := n) (B := B) (v := v) (e := e)
          (d := d) (B2 := B2) (hB2 := hB2) (hn := hn) (he := he) (hdmin := hd) (hcard := hcard')
          (hgap := hgap) (hineq := hineq)
    simpa [hB2, hq] using hfinish

