import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.projective_P
import Submission.Work.ATOM.zfree_iso_pt_biprod_zred

namespace Work.ANALYTIC

/-- The inverse left unitor of `ℤ[S]`, written through the identification `unitIso` of the
monoidal unit of `LightCondAb` with `ℤ[*]` and through the tensorator `zfreeTensorIso`, is the
image under `zmap` of the inverse left unitor of `S`. -/
theorem unitor_zfreeTensorIso (S : LightProfinite.{0}) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp
          (CategoryTheory.MonoidalCategoryStruct.leftUnitor (Work.ATOM.zfree S)).inv
          (CategoryTheory.MonoidalCategoryStruct.whiskerRight Work.ATOM.unitIso.hom
            (Work.ATOM.zfree S)))
        (Work.ATOM.zfreeTensorIso Work.ATOM.pt S).hom
      = Work.ATOM.zmap (CategoryTheory.MonoidalCategoryStruct.leftUnitor S).inv := by
  -- Both sides are the `left_unitality_inv` coherence of the lax monoidal functor
  -- `lightProfiniteToLightCondSet ⋙ free ℤ`: `zmap` is its action on morphisms, `unitIso` is
  -- its `ε`, and `zfreeTensorIso` is its `μ`.
  exact CategoryTheory.Functor.LaxMonoidal.left_unitality_inv
    (F := CategoryTheory.Functor.comp lightProfiniteToLightCondSet (LightCondensed.free ℤ)) S

end Work.ANALYTIC
