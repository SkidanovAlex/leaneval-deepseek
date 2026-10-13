import Mathlib
import Submission.Work.DSF1.Sheaf.acyclicAffineHomDefs

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

-- `haveI` is used for `Prop`-valued classes such as `PreservesFiniteLimits`; the style linter
-- prefers `have` for propositions, but the instance-cache behaviour of `haveI` is intended here.
set_option linter.style.haveILetI false

/-- Forgetting the module structure of a sheaf of `R`-modules preserves finite colimits.

A finite colimit of sheaves of modules is the sheafification (as a sheaf of modules) of the
presheaf colimit of the underlying presheaves of modules; sheafification of presheaves of
modules commutes with forgetting to abelian groups, and both the forgetful functor
`PresheafOfModules R₀ ⥤ Presheaf AddCommGrpCat` (colimits of presheaves of modules are
computed sectionwise) and the sheafification `presheafToSheaf` (a left adjoint) preserve
finite colimits. -/
instance preservesFiniteColimits_toSheaf {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  constructor
  intro D _ _
  have hLF : PreservesColimitsOfShape D
      (PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{u} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 R.obj)).symm
  constructor
  intro K
  -- Sheafification of presheaves of modules is a left adjoint whose counit is an isomorphism,
  -- so every diagram of sheaves of modules is (up to isomorphism) the image of a diagram of
  -- presheaves of modules, on which the preservation of colimits is automatic.
  set L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  set G := SheafOfModules.forget.{u} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have e : (K ⋙ G) ⋙ L ≅ K :=
    Functor.isoWhiskerLeft K
        (asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit) ≪≫
      K.rightUnitor
  have h₁ := isColimitOfPreserves L (colimit.isColimit (K ⋙ G))
  have h₂ := isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf.{u} R)
    (colimit.isColimit (K ⋙ G))
  have := preservesColimit_of_preserves_colimit_cocone (F := SheafOfModules.toSheaf.{u} R) h₁ h₂
  exact preservesColimit_of_iso_diagram _ e

theorem modStalk_preservesHomology {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    (Work.DSF1.Sheaf.modStalk X x).PreservesHomology := by
  haveI hF : PreservesFiniteLimits (Work.DSF1.Sheaf.toAbsheaf X) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  haveI hF' : PreservesFiniteColimits (Work.DSF1.Sheaf.toAbsheaf X) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  haveI hG : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
  haveI hG' : PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
  haveI : PreservesFiniteLimits (Work.DSF1.Sheaf.modStalk X x) :=
    comp_preservesFiniteLimits (Work.DSF1.Sheaf.toAbsheaf X)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  haveI : PreservesFiniteColimits (Work.DSF1.Sheaf.modStalk X x) :=
    comp_preservesFiniteColimits (Work.DSF1.Sheaf.toAbsheaf X)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  exact inferInstance

end Work.DSF1.Sheaf
