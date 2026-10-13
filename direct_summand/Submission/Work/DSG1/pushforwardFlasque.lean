import Mathlib
import Submission.Work.DSG1.Basic

namespace Work.DSG1

open CategoryTheory AlgebraicGeometry Limits

universe u

/-- The presheaf of abelian groups underlying the pushforward of `M` along `g` is the
topological pushforward of the presheaf of abelian groups underlying `M` along `g.base`. -/
lemma toSheaf_pushforward_obj {X X' : Scheme.{u}} (g : X' ⟶ X) (M : X'.Modules) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward g).obj M)).obj
      = (TopCat.Presheaf.pushforward AddCommGrpCat.{u} g.base).obj
          ((SheafOfModules.toSheaf X'.ringCatSheaf).obj M).obj := rfl

/-- Pushforward of sheaves of modules along a morphism of schemes preserves flasqueness. -/
theorem pushforwardFlasque {X X' : Scheme.{u}} (g : X' ⟶ X) (M : X'.Modules)
    (hM : TopCat.Presheaf.IsFlasque ((SheafOfModules.toSheaf X'.ringCatSheaf).obj M).obj) :
    TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward g).obj M)).obj := by
  haveI : TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X'.ringCatSheaf).obj M).obj := hM
  exact TopCat.Presheaf.IsFlasque.pushforward_isFlasque
    ((SheafOfModules.toSheaf X'.ringCatSheaf).obj M).obj g.base

end Work.DSG1
