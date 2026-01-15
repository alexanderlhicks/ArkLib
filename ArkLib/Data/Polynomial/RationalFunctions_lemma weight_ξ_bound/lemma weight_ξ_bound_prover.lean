import ArkLib.Data.Polynomial.RationalFunctions

open Polynomial
open Polynomial.Bivariate
open BCIKS20AppendixA
open BCIKS20AppendixA.ClaimA2

theorem weight_ξ_bound {F : Type} [CommRing F] [IsDomain F]
  {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)]
  (x₀ : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
  weight_Λ_over_𝒪 (BCIKS20AppendixA.ClaimA2.ξ x₀ R H) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  classical
  -- try to reduce to a lemma if exists
  simpa using (BCIKS20AppendixA.ClaimA2.weight_ξ_bound (F := F) (R := R) (H := H) x₀ (D := D) hD)

