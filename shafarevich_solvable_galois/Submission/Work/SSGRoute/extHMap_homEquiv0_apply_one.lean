import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- `Ext⁰ ≅ Hom` (Mathlib `Ext.homEquiv₀`) is inverse to `mk₀` on morphisms. -/
private lemma homEquiv₀_mk₀' {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (f : X ⟶ Y) : Abelian.Ext.homEquiv₀ (Abelian.Ext.mk₀ f) = f :=
  (Abelian.Ext.mk₀_bijective X Y).1 (by rw [Abelian.Ext.mk₀_homEquiv₀_apply])

/-- Naturality of `Ext⁰ ≅ Hom` in the *second* variable, at a degree-zero class:
`homEquiv₀ ((mk₀ f).comp z) = f ≫ homEquiv₀ z`. -/
private lemma homEquiv₀_comp_left {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (f : X ⟶ Y) (z : Abelian.Ext Y Z 0) :
    Abelian.Ext.homEquiv₀ ((Abelian.Ext.mk₀ f).comp z (zero_add 0)) =
      f ≫ Abelian.Ext.homEquiv₀ z := by
  apply (Abelian.Ext.mk₀_bijective X Z).1
  rw [Abelian.Ext.mk₀_homEquiv₀_apply]
  conv_lhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply z]
  rw [Abelian.Ext.mk₀_comp_mk₀]

/-- Naturality of `Ext⁰ ≅ Hom` in the *first* variable, at a degree-zero class:
`homEquiv₀ (z.comp (mk₀ g)) = homEquiv₀ z ≫ g`. -/
private lemma homEquiv₀_comp_right {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (z : Abelian.Ext X Y 0) (g : Y ⟶ Z) :
    Abelian.Ext.homEquiv₀ (z.comp (Abelian.Ext.mk₀ g) (add_zero 0)) =
      Abelian.Ext.homEquiv₀ z ≫ g := by
  apply (Abelian.Ext.mk₀_bijective X Z).1
  rw [Abelian.Ext.mk₀_homEquiv₀_apply]
  conv_lhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply z]
  rw [Abelian.Ext.mk₀_comp_mk₀]

/-- The unit comparison `unitRep H ⟶ res_g (unitRep G)` is the identity underlying map. -/
private lemma unitRes_apply_one {G H : Type} [Group G] [Group H] (g : H →* G) :
    SSGRoute.PTExt.unitRes g (1 : SSGRoute.PTExt.Coeff) = 1 := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply]
  simp [SSGRoute.PTExt.unitRes]

/-- `Ext⁰ ≅ Hom` on `extRes`: restriction of a degree-zero class corresponds to `resMap`. -/
private lemma homEquiv₀_extRes {G H : Type} [Group G] [Group H] (g : H →* G)
    {A : Rep.{0} SSGRoute.PTExt.Coeff G} (y : SSGRoute.PTExt.extH A 0) :
    Abelian.Ext.homEquiv₀ (SSGRoute.PTExt.extRes g y) =
      Rep.resMap g (Abelian.Ext.homEquiv₀ y) := by
  have hY : SSGRoute.PTExt.extRes g y
      = Abelian.Ext.mk₀ (Rep.resMap g (Abelian.Ext.homEquiv₀ y)) := by
    change y.mapExactFunctor (Rep.resFunctor g) = _
    conv_lhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply y]
    rw [Abelian.Ext.mapExactFunctor_mk₀]
  rw [hY, homEquiv₀_mk₀']

/-- **The value on `1` of an inflated degree-`0` class.**  For `y ∈ H⁰(G, A) = Ext⁰_G(ℤ, A)` and a
coefficient map `ι : res_g A ⟶ B`, the morphism `unitRep H ⟶ B` corresponding (via
`CategoryTheory.Abelian.Ext.homEquiv₀`) to `extHMap g ι y : H⁰(H, B)` sends `1` to `ι (y 1)`. -/
theorem extHMap_homEquiv0_apply_one {G H : Type} [Group G] [Group H] (g : H →* G)
    {A : Rep.{0} SSGRoute.PTExt.Coeff G} {B : Rep.{0} SSGRoute.PTExt.Coeff H}
    (ι : Rep.res g A ⟶ B) (y : SSGRoute.PTExt.extH A 0) :
    (CategoryTheory.Abelian.Ext.homEquiv₀ (SSGRoute.PTExt.extHMap g ι y))
        (1 : SSGRoute.PTExt.Coeff)
      = ι ((CategoryTheory.Abelian.Ext.homEquiv₀ y) (1 : SSGRoute.PTExt.Coeff)) := by
  have hY : SSGRoute.PTExt.extRes g y
      = Abelian.Ext.mk₀ (Rep.resMap g (Abelian.Ext.homEquiv₀ y)) := by
    change y.mapExactFunctor (Rep.resFunctor g) = _
    conv_lhs => rw [← Abelian.Ext.mk₀_homEquiv₀_apply y]
    rw [Abelian.Ext.mapExactFunctor_mk₀]
  have key : Abelian.Ext.homEquiv₀ (SSGRoute.PTExt.extHMap g ι y)
      = SSGRoute.PTExt.unitRes g ≫ Rep.resMap g (Abelian.Ext.homEquiv₀ y) ≫ ι := by
    change Abelian.Ext.homEquiv₀
        ((Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes g)).comp
          ((SSGRoute.PTExt.extRes g y).comp (Abelian.Ext.mk₀ ι) (add_zero 0)) (zero_add 0)) = _
    rw [hY, homEquiv₀_comp_left, homEquiv₀_comp_right, homEquiv₀_mk₀']
  rw [key, Rep.comp_apply, Rep.comp_apply, Rep.resMap_hom_apply, unitRes_apply_one]

end Work.SSGRoute
