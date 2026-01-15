import ArkLib.Data.Polynomial.RationalFunctions

open Polynomial
open Polynomial.Bivariate
open Ideal
open BCIKS20AppendixA

theorem BCIKS20AppendixA.pi_z_lift_H_tilde'_eq_zero {F : Type} [CommRing F] [IsDomain F] {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    π_z_lift (H := H) z root (H_tilde' H) = 0 := by
  classical
  -- Unfold `π_z_lift` and reduce to the defining property of `root`.
  simpa [π_z_lift] using (root.property)

theorem BCIKS20AppendixA.pi_z_lift_span_le_ker {F : Type} [CommRing F] [IsDomain F] {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    Ideal.span {H_tilde' H} ≤ RingHom.ker (π_z_lift (H := H) z root) := by
  classical
  refine
    (Ideal.span_singleton_le_iff_mem (I := RingHom.ker (π_z_lift (H := H) z root))
          (x := H_tilde' H)).2
      ?_
  exact (RingHom.mem_ker).2 (BCIKS20AppendixA.pi_z_lift_H_tilde'_eq_zero (H := H) z root)


theorem BCIKS20AppendixA.pi_z_lift_vanishes_on_span {F : Type} [CommRing F] [IsDomain F] {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    ∀ a, a ∈ Ideal.span {H_tilde' H} → π_z_lift (H := H) z root a = 0 := by
  intro a ha
  have hker : a ∈ RingHom.ker (π_z_lift (H := H) z root) :=
    (BCIKS20AppendixA.pi_z_lift_span_le_ker (F := F) (H := H) z root) ha
  exact (RingHom.mem_ker (f := π_z_lift (H := H) z root)).1 hker


namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- A `sorry`-free construction of the rational substitution map `𝒪 H →+* F`.

This is the map intended for `π_z`; it is obtained by descending `π_z_lift` to the quotient
`𝒪 H = F[X][Y] ⧸ Ideal.span {H_tilde' H}` using `Ideal.Quotient.lift`.
-/
noncomputable def pi_z_construction {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    𝒪 H →+* F := by
  classical
  refine Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift (H := H) z root) ?_
  intro a ha
  exact pi_z_lift_vanishes_on_span (H := H) z root a ha

end

end BCIKS20AppendixA

