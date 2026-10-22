import Mathlib
import Submission.Work.REFL.Basic

/-!
# AREA REFL — filtered colimits are computed sectionwise

Assume `PointwiseColimitIsSheaf`: the pointwise (presheaf) colimit of a filtered diagram of light
condensed abelian groups is again a sheaf. Then the forgetful functor
`sheafToPresheaf J D : LightCondAb ⥤ (LightProfiniteᵒᵖ ⥤ ModuleCat ℤ)` preserves filtered colimits:
its colimits are computed pointwise, and the pointwise colimit is a sheaf by hypothesis, so that
`createsColimitOfIsSheaf` applies.

Consequently `sections S = sheafToPresheaf J D ⋙ evaluation ⟨S⟩` preserves filtered colimits —
evaluation is a colimit-preserving functor since colimits of presheaves are computed pointwise —
which is the statement `SectionsFiltered`.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace Work.REFL

/-- **The key consequence of `PointwiseColimitIsSheaf`.**  The forgetful functor from light
condensed abelian groups to presheaves of abelian groups preserves colimits indexed by any small
filtered category.

Indeed, if `c` is a colimit cocone of `F ⋙ sheafToPresheaf`, then by hypothesis its cocone point is
again a sheaf, which is precisely the input of `Sheaf.createsColimitOfIsSheaf`; a functor creating
colimits of a diagram whose underlying diagram has a colimit preserves that colimit. -/
theorem sheafToPresheaf_preservesColimitsOfShape (h : PointwiseColimitIsSheaf) (J : Type)
    [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)) := by
  refine ⟨fun {K} => ?_⟩
  haveI : CreatesColimit K
      (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)) :=
    Sheaf.createsColimitOfIsSheaf K fun c hc => h J K c hc
  infer_instance

theorem sections_filtered (h : Work.REFL.PointwiseColimitIsSheaf) : Work.REFL.SectionsFiltered := by
  intro J _ _ S
  haveI : PreservesColimitsOfShape J
      (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)) :=
    sheafToPresheaf_preservesColimitsOfShape h J
  exact comp_preservesColimitsOfShape _ _

end Work.REFL
