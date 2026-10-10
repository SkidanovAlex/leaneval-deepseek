import Mathlib.Tactic.Have
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.mapExactFunctor_id
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

theorem levelPair_id {G : Type} [Group G] {M A : Rep.{0} SSGRoute.PTExt.Coeff G} {r s : ℕ}
    (x : CategoryTheory.Abelian.Ext.{0} M A r) (h : SSGRoute.PTExt.extH M s) :
    SSGRoute.PTExt.levelPair (MonoidHom.id G) (CategoryTheory.CategoryStruct.id A) x h
      = SSGRoute.PTExt.yonedaPair x h := by
  have hx : x.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = x :=
    Work.SSGRoute.mapExactFunctor_id x
  have hinner : (x.mapExactFunctor (Rep.resFunctor (MonoidHom.id G))).comp
        (CategoryTheory.Abelian.Ext.mk₀ (𝟙 A)) (add_zero r) = x := by
    rw [hx]
    exact CategoryTheory.Abelian.Ext.comp_mk₀_id x
  simp only [SSGRoute.PTExt.levelPair, SSGRoute.PTExt.yonedaPair, SSGRoute.PTExt.extRes]
  rw [hinner]

end Work.SSGRoute
