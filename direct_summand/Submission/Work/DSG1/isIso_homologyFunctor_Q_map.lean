import Mathlib
import Submission.Work.DSG1.homologyFunctor_Q_obj_iso

namespace Work.DSG1

open CategoryTheory Limits

/-- The `i`-th homology functor on the bounded below derived category, evaluated on the image of a
morphism of bounded below cochain complexes under the localization functor `Q`, is an isomorphism
on a morphism iff the complex level `i`-th homology map is.  (Naturality of
`Work.DSG1.homologyFunctor_Q_obj_iso'`.) -/
theorem isIso_homologyFunctor_Q_map {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {M N : CochainComplex.Plus C} (ψ : M ⟶ N) (i : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor C i).map (DerivedCategory.Plus.Q.map ψ)) ↔
      IsIso (HomologicalComplex.homologyMap ((CochainComplex.Plus.ι C).map ψ) i) := by
  -- The natural isomorphism exhibiting `Plus.homologyFunctor C i` after localizing as the
  -- complex-level homology functor.
  let e : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C i ≅
      CochainComplex.Plus.ι C ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.QCompιIso C)
        (DerivedCategory.homologyFunctor C i) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
        (DerivedCategory.homologyFunctorFactors C i)
  exact NatIso.isIso_map_iff e ψ

end Work.DSG1
