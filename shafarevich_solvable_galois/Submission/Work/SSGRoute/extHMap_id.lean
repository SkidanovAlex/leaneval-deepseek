import Mathlib.Combinatorics.Quiver.ReflQuiver
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

theorem extHMap_id {G : Type} [Group G] {M : Rep.{0} SSGRoute.PTExt.Coeff G} {n : ℕ}
    (y : SSGRoute.PTExt.extH M n) :
    SSGRoute.PTExt.extHMap (MonoidHom.id G)
        (CategoryTheory.CategoryStruct.id (Rep.res (MonoidHom.id G) M)) y = y := by
  have hy : y.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = y :=
    Work.SSGRoute.mapExactFunctor_id y
  have hinner :
      (y.mapExactFunctor (Rep.resFunctor (MonoidHom.id G))).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (CategoryTheory.CategoryStruct.id (Rep.res (MonoidHom.id G) M))) (add_zero n) = y := by
    rw [hy]
    exact CategoryTheory.Abelian.Ext.comp_mk₀_id y
  have houter :
      (CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes (MonoidHom.id G))).comp y
        (zero_add n) = y := by
    rw [show SSGRoute.PTExt.unitRes (MonoidHom.id G) = 𝟙 (SSGRoute.PTExt.unitRep G) from rfl]
    exact CategoryTheory.Abelian.Ext.mk₀_id_comp y
  simp only [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extRes]
  rw [hinner, houter]

end Work.SSGRoute
