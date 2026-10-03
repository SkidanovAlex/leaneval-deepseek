/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Left derived functors commute with exact functors.
-/
import Mathlib
import Submission.Work.ORHomAlg.Bridge.homology_mapHomologicalComplex

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits

namespace Work.ORHomAlg.Bridge

universe u v w

/-- If `G : D ⥤ E` is an additive functor between abelian categories which preserves homology
(i.e. is exact), then for any additive functor `F : C ⥤ D` out of a category with projective
resolutions, the left derived functors of the composite `F ⋙ G` are obtained by applying `G`
to the left derived functors of `F`. -/
theorem leftDerived_comp_of_exactFunctor {C : Type u} [Category.{v} C] [Abelian C]
    [HasProjectiveResolutions C] {D : Type u} [Category.{v} D] [Abelian D]
    {E : Type u} [Category.{v} E] [Abelian E]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
    (X : C) (n : ℕ) :
    Nonempty (G.obj ((F.leftDerived n).obj X) ≅ ((F ⋙ G).leftDerived n).obj X) := by
  have : CategoryWithHomology D := inferInstance
  have : CategoryWithHomology E := inferInstance
  let P := projectiveResolution X
  let K : HomologicalComplex D (ComplexShape.down ℕ) :=
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have e1 := ProjectiveResolution.isoLeftDerivedObj P F n
  have e2 := ShortComplex.mapHomologyIso (K.sc n) G
  have e3 := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)
  have e4 := ProjectiveResolution.isoLeftDerivedObj P (F ⋙ G) n
  exact ⟨G.mapIso e1 ≪≫ e2.symm ≪≫
    (((HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).mapIso
      ((e3.app P.complex).symm)).symm) ≪≫ e4.symm⟩

end Work.ORHomAlg.Bridge
