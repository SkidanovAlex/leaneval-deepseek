import Mathlib
import Submission.Work.DSMap.Map

namespace Work.DSEQP

universe u

open CategoryTheory

/-- For a cochain complex of `R`-modules indexed by `ℕ`, the `0`-th homology is the kernel of
the differential `d 0 1`: there is no negative-degree term, so the incoming differential is
zero and the homology is the group of `0`-cycles.

The identification is the composite of the canonical isomorphisms
`K.homology 0 ≅ K.cycles 0` (`CochainComplex.isoHomologyπ₀`) and
`K.cycles 0 ≅ LinearMap.ker (K.d 0 1)` (`ShortComplex.moduleCatCyclesIso`). -/
theorem cochainComplex_homology_zero_iso_ker {R : Type*} [CommRing R]
    (K : CochainComplex (ModuleCat R) ℕ) :
    Nonempty (K.homology 0 ≃ₗ[R] LinearMap.ker (K.d 0 1).hom) := by
  refine ⟨?_⟩
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by
    apply ComplexShape.next_eq'
    exact ComplexShape.up_mk 0 1 (by norm_num)
  have hker : LinearMap.ker (K.d 0 ((ComplexShape.up ℕ).next 0)).hom
      = LinearMap.ker (K.d 0 1).hom := by rw [hnext]
  refine (Iso.toLinearEquiv ((CochainComplex.isoHomologyπ₀ K).symm ≪≫
    ShortComplex.moduleCatCyclesIso (K.sc 0))).trans (LinearEquiv.ofEq _ _ hker)

theorem cech_homology_zero_iso_ker {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)} {ι : Type u} (U : ι → X.Opens) :
    Nonempty ((DSMap.cech A X f U).homology 0 ≃ₗ[A]
      LinearMap.ker ((DSMap.cech A X f U).d 0 1).hom) :=
  cochainComplex_homology_zero_iso_ker (DSMap.cech A X f U)

end Work.DSEQP
