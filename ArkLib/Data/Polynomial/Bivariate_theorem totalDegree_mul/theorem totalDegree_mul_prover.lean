import Mathlib.Data.Finset.NatAntidiagonal
import ArkLib.Data.Polynomial.Prelims
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Finset.Max

open scoped BigOperators
open scoped Polynomial.Bivariate
open Polynomial
open Polynomial.Bivariate

theorem Polynomial.Bivariate.antidiagonal_ne_lt_fst_or_lt_snd {a b i j : ℕ} (h : (i, j) ∈ Finset.antidiagonal (a + b)) (hne : (i, j) ≠ (a, b)) :
    a < i ∨ b < j := by
  classical
  have hij : i + j = a + b := by
    simpa [Finset.mem_antidiagonal] using h
  by_contra hcontra
  have hia : i ≤ a := by
    have : ¬a < i := by
      intro hai
      exact hcontra (Or.inl hai)
    exact Nat.le_of_not_gt this
  have hjb : j ≤ b := by
    have : ¬b < j := by
      intro hbj
      exact hcontra (Or.inr hbj)
    exact Nat.le_of_not_gt this
  have hj_ge : b ≤ j := by
    have hib : i + b ≤ a + b := Nat.add_le_add_right hia b
    have hib' : i + b ≤ i + j := by
      simpa [← hij] using hib
    exact Nat.le_of_add_le_add_left hib'
  have hj_eq : j = b := le_antisymm hjb hj_ge
  have hi_eq : i = a := by
    have : i + b = a + b := by
      simpa [hj_eq] using hij
    exact Nat.add_right_cancel this
  have hprod : (i, j) = (a, b) := by
    ext
    · exact hi_eq
    · exact hj_eq
  exact hne hprod

theorem Polynomial.Bivariate.natDegree_sum_eq_of_unique {F : Type*} [Semiring F] {α : Type*} {s : Finset α} {f : α → F[X]} {deg : ℕ}
  (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  classical
  intro hmx_deg hothers
  by_cases hdeg0 : deg = 0
  · subst hdeg0
    have hz : ∀ y ∈ s, y ≠ mx → f y = 0 := by
      intro y hy hyne
      rcases hothers y hy hyne with hlt | hzero
      · exfalso
        exact Nat.not_lt_zero _ hlt
      · exact hzero
    have hsum : (∑ x ∈ s, f x) = f mx := by
      classical
      refine Finset.sum_eq_single_of_mem (f := fun x => f x) mx h ?_
      intro y hy hyne
      exact hz y hy hyne
    simpa [hsum] using hmx_deg
  ·
    have hmx_ne0 : f mx ≠ 0 := by
      intro h0
      have : deg = 0 := by
        simpa [h0] using hmx_deg.symm
      exact hdeg0 this
    have hbot_lt : (⊥ : WithBot ℕ) < (f mx).degree := by
      rw [Polynomial.degree_eq_natDegree hmx_ne0]
      exact WithBot.bot_lt_coe (f mx).natDegree
    have hsup : (s.erase mx).sup (fun b => (f b).degree) < (f mx).degree := by
      refine (Finset.sup_lt_iff hbot_lt).2 ?_
      intro b hb
      have hb_ne : b ≠ mx := (Finset.mem_erase.mp hb).1
      have hb_s : b ∈ s := (Finset.mem_erase.mp hb).2
      rcases hothers b hb_s hb_ne with hlt | hzero
      ·
        have hnat : (f b).natDegree < (f mx).natDegree := by
          have hdeg' : deg = (f mx).natDegree := by
            simpa using hmx_deg.symm
          exact lt_of_lt_of_eq hlt hdeg'
        exact Polynomial.degree_lt_degree hnat
      ·
        simpa [hzero] using hbot_lt
    have hrest : (∑ x ∈ s.erase mx, f x).degree < (f mx).degree := by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le (s := s.erase mx) (f := f)) hsup
    have hsum : (∑ x ∈ s, f x) = (∑ x ∈ s.erase mx, f x) + f mx := by
      simpa using (Finset.sum_erase_add (s := s) (f := fun x => f x) h).symm
    calc
      (∑ x ∈ s, f x).natDegree = ((∑ x ∈ s.erase mx, f x) + f mx).natDegree := by
        simpa [hsum]
      _ = (f mx).natDegree := by
        exact Polynomial.natDegree_add_eq_right_of_degree_lt hrest
      _ = deg := hmx_deg

def Polynomial.Bivariate.totalDegree {F : Type*} [Semiring F] (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natDegree + m)

theorem Polynomial.Bivariate.exists_maximizer_totalDegree {F : Type*} [Semiring F] {f : F[X][Y]} (hf : f ≠ 0) :
    ∃ mm : ℕ, mm ∈ f.support ∧
      (f.coeff mm).natDegree + mm = totalDegree f ∧
      (∀ m : ℕ, m ∈ f.support → (f.coeff m).natDegree + m = totalDegree f → m ≤ mm) := by
  classical
  let g : ℕ → ℕ := fun m => (f.coeff m).natDegree + m
  have hsupp : f.support.Nonempty := by
    exact (Polynomial.support_nonempty.2 hf)
  obtain ⟨m0, hm0_mem, hm0_sup⟩ := Finset.exists_mem_eq_sup f.support hsupp g
  have hm0_g : g m0 = totalDegree f := by
    have : totalDegree f = g m0 := by
      simpa [Polynomial.Bivariate.totalDegree, g] using hm0_sup
    exact this.symm
  let S : Finset ℕ := f.support.filter (fun m => g m = totalDegree f)
  have hS_nonempty : S.Nonempty := by
    refine ⟨m0, ?_⟩
    simp [S, hm0_mem, hm0_g]
  let mm : ℕ := S.max' hS_nonempty
  have hmm_mem_S : mm ∈ S := by
    simpa [mm] using (Finset.max'_mem S hS_nonempty)
  have hmm_mem_support : mm ∈ f.support := by
    have h : mm ∈ f.support ∧ g mm = totalDegree f := by
      simpa [S] using hmm_mem_S
    exact h.1
  have hmm_g : g mm = totalDegree f := by
    have h : mm ∈ f.support ∧ g mm = totalDegree f := by
      simpa [S] using hmm_mem_S
    exact h.2
  refine ⟨mm, hmm_mem_support, ?_, ?_⟩
  · simpa [g] using hmm_g
  · intro m hm_mem hm_gm
    have hm_mem_S : m ∈ S := by
      -- unfold `g` so that `hm_gm` matches
      simp [S, hm_mem, hm_gm, g]
    have hgreat : IsGreatest (↑S : Set ℕ) (S.max' hS_nonempty) := Finset.isGreatest_max' S hS_nonempty
    have hm_le : m ≤ S.max' hS_nonempty := hgreat.2 hm_mem_S
    simpa [mm] using hm_le

theorem Polynomial.Bivariate.totalDegree_mul_ge {F : Type*} [Semiring F] [IsDomain F] {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree f + totalDegree g ≤ totalDegree (f * g) := by
  classical
  -- choose indices maximizing the total-degree contribution
  obtain ⟨mmf, hmmf_mem, hmmf_eq, hmmf_max⟩ :=
    Polynomial.Bivariate.exists_maximizer_totalDegree (f := f) hf
  obtain ⟨mmg, hmmg_mem, hmmg_eq, hmmg_max⟩ :=
    Polynomial.Bivariate.exists_maximizer_totalDegree (f := g) hg

  have hmmf_coeff_ne0 : f.coeff mmf ≠ 0 := (Polynomial.mem_support_iff).1 hmmf_mem
  have hmmg_coeff_ne0 : g.coeff mmg ≠ 0 := (Polynomial.mem_support_iff).1 hmmg_mem

  -- convenient notation
  let tf : ℕ → ℕ := fun m => (f.coeff m).natDegree + m
  let tg : ℕ → ℕ := fun m => (g.coeff m).natDegree + m

  let n0 : ℕ := mmf + mmg
  let deg : ℕ := (f.coeff mmf).natDegree + (g.coeff mmg).natDegree

  have hcoeff_mul : (f * g).coeff n0 =
      ∑ x ∈ Finset.antidiagonal n0, f.coeff x.1 * g.coeff x.2 := by
    simpa using (Polynomial.coeff_mul f g n0)

  have hmx_mem : (mmf, mmg) ∈ Finset.antidiagonal n0 := by
    simp [n0]

  have hmx_natdeg : (f.coeff mmf * g.coeff mmg).natDegree = deg := by
    simpa [deg] using
      (Polynomial.natDegree_mul (p := f.coeff mmf) (q := g.coeff mmg) hmmf_coeff_ne0
        hmmg_coeff_ne0)

  have hother :
      ∀ y ∈ Finset.antidiagonal n0, y ≠ (mmf, mmg) →
        (f.coeff y.1 * g.coeff y.2).natDegree < deg ∨ f.coeff y.1 * g.coeff y.2 = 0 := by
    intro y hy hne
    have hlt : mmf < y.1 ∨ mmg < y.2 := by
      have hy' : (y.1, y.2) ∈ Finset.antidiagonal (mmf + mmg) := by
        simpa [n0] using hy
      have hne' : (y.1, y.2) ≠ (mmf, mmg) := by
        simpa using hne
      simpa using
        (Polynomial.Bivariate.antidiagonal_ne_lt_fst_or_lt_snd (a := mmf) (b := mmg) (i := y.1)
          (j := y.2) hy' hne')

    by_cases hzero : f.coeff y.1 * g.coeff y.2 = 0
    · exact Or.inr hzero
    · left
      have hfcoeff_ne0 : f.coeff y.1 ≠ 0 := by
        intro hf0
        apply hzero
        simp [hf0]
      have hgcoeff_ne0 : g.coeff y.2 ≠ 0 := by
        intro hg0
        apply hzero
        simp [hg0]

      have hy1_mem : y.1 ∈ f.support := (Polynomial.mem_support_iff).2 hfcoeff_ne0
      have hy2_mem : y.2 ∈ g.support := (Polynomial.mem_support_iff).2 hgcoeff_ne0

      have htf_le : tf y.1 ≤ totalDegree f := by
        simpa [Polynomial.Bivariate.totalDegree, tf] using
          (Finset.le_sup (f := fun m : ℕ => (f.coeff m).natDegree + m) hy1_mem)
      have htg_le : tg y.2 ≤ totalDegree g := by
        simpa [Polynomial.Bivariate.totalDegree, tg] using
          (Finset.le_sup (f := fun m : ℕ => (g.coeff m).natDegree + m) hy2_mem)

      have hij : y.1 + y.2 = n0 := by
        simpa using (Finset.mem_antidiagonal.mp hy)

      have hsum_lt : tf y.1 + tg y.2 < totalDegree f + totalDegree g := by
        cases hlt with
        | inl hmmf_lt =>
            have htf_ne : tf y.1 ≠ totalDegree f := by
              intro heq
              have hy1_le : y.1 ≤ mmf := hmmf_max y.1 hy1_mem (by simpa [tf] using heq)
              exact (Nat.not_lt_of_ge hy1_le) hmmf_lt
            have htf_lt : tf y.1 < totalDegree f := lt_of_le_of_ne htf_le htf_ne
            exact Nat.add_lt_add_of_lt_of_le htf_lt htg_le
        | inr hmmg_lt =>
            have htg_ne : tg y.2 ≠ totalDegree g := by
              intro heq
              have hy2_le : y.2 ≤ mmg := hmmg_max y.2 hy2_mem (by simpa [tg] using heq)
              exact (Nat.not_lt_of_ge hy2_le) hmmg_lt
            have htg_lt : tg y.2 < totalDegree g := lt_of_le_of_ne htg_le htg_ne
            exact Nat.add_lt_add_of_le_of_lt htf_le htg_lt

      have htf_tg_eq :
          tf y.1 + tg y.2 =
            ((f.coeff y.1).natDegree + (g.coeff y.2).natDegree) + n0 := by
        calc
          tf y.1 + tg y.2 = ((f.coeff y.1).natDegree + y.1) + ((g.coeff y.2).natDegree + y.2) := by
            rfl
          _ = ((f.coeff y.1).natDegree + (g.coeff y.2).natDegree) + (y.1 + y.2) := by
            ac_rfl
          _ = ((f.coeff y.1).natDegree + (g.coeff y.2).natDegree) + n0 := by
            simpa [hij]

      have htot_eq : totalDegree f + totalDegree g = deg + n0 := by
        calc
          totalDegree f + totalDegree g =
              ((f.coeff mmf).natDegree + mmf) + ((g.coeff mmg).natDegree + mmg) := by
                simp [hmmf_eq.symm, hmmg_eq.symm]
          _ = ((f.coeff mmf).natDegree + (g.coeff mmg).natDegree) + (mmf + mmg) := by
                ac_rfl
          _ = deg + n0 := by
                simp [deg, n0]

      have h' :
          ((f.coeff y.1).natDegree + (g.coeff y.2).natDegree) + n0 < deg + n0 := by
        simpa [htf_tg_eq, htot_eq] using hsum_lt

      have hdeg_lt : (f.coeff y.1).natDegree + (g.coeff y.2).natDegree < deg :=
        Nat.lt_of_add_lt_add_right h'

      have hnatdeg_le :
          (f.coeff y.1 * g.coeff y.2).natDegree ≤
            (f.coeff y.1).natDegree + (g.coeff y.2).natDegree := by
        simpa using
          (Polynomial.natDegree_mul_le (p := f.coeff y.1) (q := g.coeff y.2))

      exact lt_of_le_of_lt hnatdeg_le hdeg_lt

  have hnatdeg_coeff : ((f * g).coeff n0).natDegree = deg := by
    have hsum :=
      Polynomial.Bivariate.natDegree_sum_eq_of_unique (F := F) (s := Finset.antidiagonal n0)
        (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2) (deg := deg) (mx := (mmf, mmg))
        hmx_mem hmx_natdeg hother
    simpa [hcoeff_mul] using hsum

  -- show the coefficient is nonzero (hence n0 is in the support)
  have hcoeff_ne0 : (f * g).coeff n0 ≠ 0 := by
    -- show its X^deg coefficient is nonzero
    have hmain_ne0 : f.coeff mmf * g.coeff mmg ≠ 0 := mul_ne_zero hmmf_coeff_ne0 hmmg_coeff_ne0
    have hmain_lc_ne0 : (f.coeff mmf * g.coeff mmg).leadingCoeff ≠ 0 :=
      (Polynomial.leadingCoeff_ne_zero).2 hmain_ne0
    have hmain_coeff_deg :
        (f.coeff mmf * g.coeff mmg).coeff deg = (f.coeff mmf * g.coeff mmg).leadingCoeff := by
      simpa [hmx_natdeg] using (Polynomial.coeff_natDegree (p := f.coeff mmf * g.coeff mmg))
    have hmain_coeff_deg_ne0 : (f.coeff mmf * g.coeff mmg).coeff deg ≠ 0 := by
      simpa [hmain_coeff_deg] using hmain_lc_ne0

    have hcoeff_deg_ne0 : ((f * g).coeff n0).coeff deg ≠ 0 := by
      -- rewrite as a finite sum and take X^deg coefficient
      rw [hcoeff_mul]
      have hcoeff_sum :
          (∑ x ∈ Finset.antidiagonal n0, f.coeff x.1 * g.coeff x.2).coeff deg =
            ∑ x ∈ Finset.antidiagonal n0, (f.coeff x.1 * g.coeff x.2).coeff deg := by
        simpa using
          (Polynomial.finset_sum_coeff (s := Finset.antidiagonal n0)
            (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2) (n := deg))
      -- convert to the coefficient-sum form
      rw [hcoeff_sum]
      -- all terms except (mmf,mmg) vanish at X^deg
      have hvanish :
          ∀ y ∈ Finset.antidiagonal n0, y ≠ (mmf, mmg) →
            (f.coeff y.1 * g.coeff y.2).coeff deg = 0 := by
        intro y hy hne
        have hy' := hother y hy hne
        rcases hy' with hylt | hyzero
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt hylt
        · simp [hyzero]
      have hsum_single :
          (∑ x ∈ Finset.antidiagonal n0, (f.coeff x.1 * g.coeff x.2).coeff deg) =
            (f.coeff mmf * g.coeff mmg).coeff deg := by
        refine Finset.sum_eq_single_of_mem (a := (mmf, mmg)) hmx_mem ?_
        intro y hy hne
        exact hvanish y hy hne
      -- finish
      simpa [hsum_single] using hmain_coeff_deg_ne0

    intro h0
    apply hcoeff_deg_ne0
    simpa [h0]

  have hn0_mem : n0 ∈ (f * g).support := (Polynomial.mem_support_iff).2 hcoeff_ne0

  have hle_sup :
      ((f * g).coeff n0).natDegree + n0 ≤ totalDegree (f * g) := by
    simpa [Polynomial.Bivariate.totalDegree] using
      (Finset.le_sup (f := fun m : ℕ => ((f * g).coeff m).natDegree + m) hn0_mem)

  have htot_eq : totalDegree f + totalDegree g = deg + n0 := by
    calc
      totalDegree f + totalDegree g =
          ((f.coeff mmf).natDegree + mmf) + ((g.coeff mmg).natDegree + mmg) := by
            simp [hmmf_eq.symm, hmmg_eq.symm]
      _ = ((f.coeff mmf).natDegree + (g.coeff mmg).natDegree) + (mmf + mmg) := by
            ac_rfl
      _ = deg + n0 := by
            simp [deg, n0]

  -- conclude using the specific index n0 in the supremum
  calc
    totalDegree f + totalDegree g = deg + n0 := htot_eq
    _ = ((f * g).coeff n0).natDegree + n0 := by
          simpa [hnatdeg_coeff]
    _ ≤ totalDegree (f * g) := hle_sup

theorem Polynomial.Bivariate.totalDegree_mul_le {F : Type*} [Semiring F] (f g : F[X][Y]) :
    totalDegree (f * g) ≤ totalDegree f + totalDegree g := by
  classical
  unfold Polynomial.Bivariate.totalDegree
  refine (Finset.sup_le_iff).2 ?_
  intro n hn
  set Tf : ℕ := f.support.sup (fun m => (f.coeff m).natDegree + m) with hTf
  set Tg : ℕ := g.support.sup (fun m => (g.coeff m).natDegree + m) with hTg
  set T : ℕ := Tf + Tg with hT
  have hn0 : (f * g).coeff n ≠ 0 := by
    simpa [Polynomial.mem_support_iff] using hn
  have hsum_ne_zero : (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2) ≠ 0 := by
    simpa [Polynomial.coeff_mul] using hn0
  rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne_zero with ⟨x, hx, hx0⟩
  rcases x with ⟨i, j⟩
  have hij : i + j = n := by
    simpa [Finset.mem_antidiagonal] using hx
  have hfi0 : f.coeff i ≠ 0 := by
    intro h
    apply hx0
    simp [h]
  have hgj0 : g.coeff j ≠ 0 := by
    intro h
    apply hx0
    simp [h]
  have hi_mem : i ∈ f.support := (Polynomial.mem_support_iff).2 hfi0
  have hj_mem : j ∈ g.support := (Polynomial.mem_support_iff).2 hgj0
  have hi_sup : (f.coeff i).natDegree + i ≤ Tf := by
    simpa [hTf] using
      (Finset.le_sup (s := f.support) (f := fun m => (f.coeff m).natDegree + m) hi_mem)
  have hj_sup : (g.coeff j).natDegree + j ≤ Tg := by
    simpa [hTg] using
      (Finset.le_sup (s := g.support) (f := fun m => (g.coeff m).natDegree + m) hj_mem)
  have hi_le : i ≤ Tf :=
    le_trans (Nat.le_add_left i (f.coeff i).natDegree) hi_sup
  have hj_le : j ≤ Tg :=
    le_trans (Nat.le_add_left j (g.coeff j).natDegree) hj_sup
  have hn_le : n ≤ T := by
    have : i + j ≤ Tf + Tg := Nat.add_le_add hi_le hj_le
    simpa [hT, hij] using this
  have hdeg : ((f * g).coeff n).natDegree ≤ T - n := by
    -- Expand the coefficient via `coeff_mul` and bound each summand.
    --
    -- We use `Polynomial.natDegree_sum_le_of_forall_le`.
    --
    simpa [Polynomial.coeff_mul] using
      (Polynomial.natDegree_sum_le_of_forall_le (s := Finset.antidiagonal n)
        (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2) (n := T - n) (by
          intro x hx
          rcases x with ⟨a, b⟩
          have hab : a + b = n := by
            simpa [Finset.mem_antidiagonal] using hx
          by_cases hfa : f.coeff a = 0
          · -- then the product is zero
            simp [hfa]
          · by_cases hgb : g.coeff b = 0
            · simp [hgb]
            ·
              have ha_mem : a ∈ f.support := (Polynomial.mem_support_iff).2 hfa
              have hb_mem : b ∈ g.support := (Polynomial.mem_support_iff).2 hgb
              have ha_sup : (f.coeff a).natDegree + a ≤ Tf := by
                simpa [hTf] using
                  (Finset.le_sup (s := f.support)
                    (f := fun m => (f.coeff m).natDegree + m) ha_mem)
              have hb_sup : (g.coeff b).natDegree + b ≤ Tg := by
                simpa [hTg] using
                  (Finset.le_sup (s := g.support)
                    (f := fun m => (g.coeff m).natDegree + m) hb_mem)
              have ha_deg : (f.coeff a).natDegree ≤ Tf - a :=
                le_tsub_of_add_le_right ha_sup
              have hb_deg : (g.coeff b).natDegree ≤ Tg - b :=
                le_tsub_of_add_le_right hb_sup
              have hmul : (f.coeff a * g.coeff b).natDegree ≤ (Tf - a) + (Tg - b) :=
                Polynomial.natDegree_mul_le_of_le ha_deg hb_deg
              have ha_le_Tf : a ≤ Tf :=
                le_trans (Nat.le_add_left a (f.coeff a).natDegree) ha_sup
              have hb_le_Tg : b ≤ Tg :=
                le_trans (Nat.le_add_left b (g.coeff b).natDegree) hb_sup
              have htsub : (Tf - a) + (Tg - b) = T - n := by
                calc
                  Tf - a + (Tg - b) = Tf + Tg - (a + b) := by
                    simpa using
                      (tsub_add_tsub_comm (a := Tf) (b := a) (c := Tg) (d := b) ha_le_Tf hb_le_Tg)
                  _ = Tf + Tg - n := by
                    simpa [hab]
                  _ = T - n := by
                    simpa [hT]
              simpa [htsub] using hmul))
  have : ((f * g).coeff n).natDegree + n ≤ T := by
    calc
      ((f * g).coeff n).natDegree + n ≤ (T - n) + n := by
        exact Nat.add_le_add_right hdeg n
      _ = T := by
        exact Nat.sub_add_cancel hn_le
  simpa [hT, hTf, hTg] using this


theorem Polynomial.Bivariate.totalDegree_mul {F : Type*} [Semiring F] [IsDomain F] {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  exact le_antisymm (Polynomial.Bivariate.totalDegree_mul_le (f := f) (g := g))
    (Polynomial.Bivariate.totalDegree_mul_ge (f := f) (g := g) hf hg)


