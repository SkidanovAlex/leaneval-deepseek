import Mathlib
import Submission.Work.ORHomAlg.Tor

open CategoryTheory

namespace Work.ORHomAlg

universe u v

/-- If an additive functor `F : C ⥤ D` preserves projective objects and homology, then for any
additive `G : D ⥤ E` the left derived functors of `F ⋙ G` are obtained by applying the left
derived functors of `G` to `F`. -/
theorem leftDerived_comp_of_preservesProjectiveObjects
    {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
    {D : Type u} [Category.{v} D] [Abelian D] [HasProjectiveResolutions D]
    {E : Type u} [Category.{v} E] [Abelian E]
    (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
    (G : D ⥤ E) [G.Additive] (X : C) (n : ℕ) :
    Nonempty (((F ⋙ G).leftDerived n).obj X ≅ (G.leftDerived n).obj (F.obj X)) := by
  -- Choose a projective resolution `P` of `X`.  Since `F` preserves projective objects and
  -- homology, `F.mapProjectiveResolution P` is a projective resolution of `F.obj X`.
  let P : ProjectiveResolution X := projectiveResolution X
  let P' : ProjectiveResolution (F.obj X) := F.mapProjectiveResolution P
  -- `leftDerived` can be computed from any projective resolution, so both sides identify with
  -- the `n`-th homology of `G` applied to the complex `F.mapHomologicalComplex _ P.complex`;
  -- the identification `(F ⋙ G).mapHomologicalComplex = F.mapHomologicalComplex ⋙ G.mapHomologicalComplex`
  -- closes the gap.
  refine ⟨(P.isoLeftDerivedObj (F ⋙ G) n) ≪≫ ?_ ≪≫ (P'.isoLeftDerivedObj G n).symm⟩
  exact (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).mapIso
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.down ℕ)).app P.complex).symm

end Work.ORHomAlg
