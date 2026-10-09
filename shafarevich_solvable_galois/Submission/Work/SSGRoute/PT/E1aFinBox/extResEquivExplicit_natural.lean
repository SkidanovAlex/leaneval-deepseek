import Mathlib
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of `extResEquivExplicit` in the coefficient

`extResEquivExplicit e X Y` (`E1aClean/finPlaceDict.lean`) is by definition the inverse of the
`res`-functoriality bijection `(Rep.resFunctor e.symm.toMonoidHom).mapExtAddHom X Y 1` on `Ext¹`.
This file records that this inverse is natural in its contravariant first (coefficient) variable.

It is a brick of the coefficient naturality chase of the finite-place dictionary `E1aClean.phiCan`
(see `Submission/Work/SSGRoute/E1aClean/finPlaceDictHolds.lean`, obligation (A)/(B)); its proof is
`F.mapExtAddHom`'s compatibility with `mk₀` transported across the inverse.
-/

open CategoryTheory

namespace Work.SSGRoute.PT.E1aFinBox

/-- For `e : G ≃* G'`, `g : X₂ ⟶ X₁` in `Rep Coeff G` and `z : Ext (res e.symm X₁) (res e.symm Y) 1`,
`extResEquivExplicit e X₂ Y ((mk₀ (Rep.resMap e.symm g)).comp z (zero_add 1)) =
 (mk₀ g).comp (extResEquivExplicit e X₁ Y z) (zero_add 1)`. -/
theorem extResEquivExplicit_natural {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X₁ X₂ Y : Rep.{0} SSGRoute.PTExt.Coeff G) (g : X₂ ⟶ X₁)
    (z : CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X₁)
      (Rep.res e.symm.toMonoidHom Y) 1) :
    Work.SSGRoute.E1aClean.extResEquivExplicit e X₂ Y
        ((CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap e.symm.toMonoidHom g)).comp z (zero_add 1))
      = (CategoryTheory.Abelian.Ext.mk₀ g).comp
          (Work.SSGRoute.E1aClean.extResEquivExplicit e X₁ Y z) (zero_add 1) := by
  have hAB : (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap e.symm.toMonoidHom g)).comp z (zero_add 1)
      = (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X₂ Y 1
          ((CategoryTheory.Abelian.Ext.mk₀ g).comp
            ((Work.SSGRoute.E1aClean.extResEquivExplicit e X₁ Y) z) (zero_add 1)) := by
    rw [Functor.mapExtAddHom_apply, CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
      CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
    change (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap e.symm.toMonoidHom g)).comp z (zero_add 1)
      = (CategoryTheory.Abelian.Ext.mk₀
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).map g)).comp
          ((Work.SSGRoute.E1aClean.extResEquivExplicit e X₁ Y).symm
            ((Work.SSGRoute.E1aClean.extResEquivExplicit e X₁ Y) z)) (zero_add 1)
    rw [AddEquiv.symm_apply_apply]
  exact (Work.SSGRoute.E1aClean.extResEquivExplicit e X₂ Y).symm.injective (by
    rw [AddEquiv.symm_apply_apply]
    change (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap e.symm.toMonoidHom g)).comp z (zero_add 1)
      = (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X₂ Y 1
          ((CategoryTheory.Abelian.Ext.mk₀ g).comp
            ((Work.SSGRoute.E1aClean.extResEquivExplicit e X₁ Y) z) (zero_add 1))
    exact hAB)

end Work.SSGRoute.PT.E1aFinBox
