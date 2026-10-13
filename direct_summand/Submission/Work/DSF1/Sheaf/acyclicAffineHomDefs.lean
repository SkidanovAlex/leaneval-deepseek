import Mathlib
import ChallengeDeps
import Submission.Work.DSF1.Sheaf.CechSheaf

/-!
# Vocabulary for the acyclicity of the Čech terms along an affine open immersion

This file collects the (axiom-clean) definitions used by the proof of
`Work.DSF1.Sheaf.secSheaf_acyclic_affineHom`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- Global sections `Γ(X, ⊤)` of sheaves of `𝒪_X`-modules, as a functor. -/
noncomputable abbrev gammaTop (X : Scheme.{u}) :
    X.Modules ⥤ ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))) :=
  SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))

/-- Pushforward along the open immersion of an open subscheme. -/
noncomputable abbrev pushforwardι {X : Scheme.{u}} (W : X.Opens) :
    W.toScheme.Modules ⥤ X.Modules :=
  Scheme.Modules.pushforward W.ι

/-- The structure sheaf of an open subscheme, as a module over itself. -/
noncomputable abbrev unitSheaf {X : Scheme.{u}} (W : X.Opens) : W.toScheme.Modules :=
  SheafOfModules.unit W.toScheme.ringCatSheaf

/-- The underlying sheaf of abelian groups of a sheaf of `𝒪_X`-modules. -/
noncomputable abbrev toAbsheaf (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat :=
  SheafOfModules.toSheaf X.ringCatSheaf

/-- The stalk of a sheaf of `𝒪_X`-modules at a point, as a functor. -/
noncomputable abbrev modStalk (X : Scheme.{u}) (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  toAbsheaf X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- The sections functor `Γ(U, -)` of sheaves of `𝒪_X`-modules, as abelian groups. -/
noncomputable def sectionsFunctor (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  toAbsheaf X ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    (CategoryTheory.evaluation (TopologicalSpace.Opens X.toTopCat)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opposite.op U))

/-- The sections functor, unfolded at an object (`rfl`). -/
@[simp]
lemma sectionsFunctor_obj (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) :
    (sectionsFunctor X U).obj M =
      ((toAbsheaf X).obj M).1.obj (Opposite.op U) := rfl

section Additive

instance (X : Scheme.{u}) : (gammaTop X).Additive :=
  inferInstanceAs ((SheafOfModules.evaluation X.ringCatSheaf
    (Opposite.op (⊤ : X.Opens))).Additive)

instance (X : Scheme.{u}) : (toAbsheaf X).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf X.ringCatSheaf).Additive)

instance (X : Scheme.{u}) (x : X) : (modStalk X x).Additive :=
  inferInstanceAs ((toAbsheaf X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive)

/-- The sections functor preserves zero morphisms (all that `mapHomologicalComplex` needs). -/
instance (X : Scheme.{u}) (U : X.Opens) : (sectionsFunctor X U).PreservesZeroMorphisms where
  map_zero A B := by
    change ((toAbsheaf X).map (0 : A ⟶ B)).hom.app (Opposite.op U) = 0
    rw [(toAbsheaf X).map_zero A B]
    rfl

end Additive

end Work.DSF1.Sheaf
