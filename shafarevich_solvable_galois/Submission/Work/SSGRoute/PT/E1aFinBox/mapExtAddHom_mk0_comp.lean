import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `F.mapExtAddHom` commutes with precomposition by `Ext.mk₀`

A two-line corollary of Mathlib's `Ext.mapExactFunctor_comp` and `Ext.mapExactFunctor_mk₀`
(`Mathlib/Algebra/Homology/DerivedCategory/Ext/Map.lean`).  It is the first brick of the coefficient
naturality chase of the finite-place dictionary `E1aClean.phiCan` (see
`Submission/Work/SSGRoute/E1aClean/finPlaceDictHolds.lean`, obligation (A)/(B)).
-/

open CategoryTheory

namespace Work.SSGRoute.PT.E1aFinBox

/-- For an additive functor `F` between abelian categories with `Ext`, `g : X₂ ⟶ X₁` and
`w : Ext X₁ Y 1`,
`F.mapExtAddHom X₂ Y 1 ((mk₀ g).comp w (zero_add 1)) =
 (mk₀ (F.map g)).comp (F.mapExtAddHom X₁ Y 1 w) (zero_add 1)`. -/
theorem mapExtAddHom_mk0_comp {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C] [CategoryTheory.Category D]
    [CategoryTheory.Abelian D] [CategoryTheory.HasExt D] (F : CategoryTheory.Functor C D)
    [CategoryTheory.Functor.Additive F]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X₁ X₂ Y : C} (g : X₂ ⟶ X₁) (w : CategoryTheory.Abelian.Ext X₁ Y 1) :
    F.mapExtAddHom X₂ Y 1 ((CategoryTheory.Abelian.Ext.mk₀ g).comp w (zero_add 1))
      = (CategoryTheory.Abelian.Ext.mk₀ (F.map g)).comp
          (F.mapExtAddHom X₁ Y 1 w) (zero_add 1) := by
  rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply,
    CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]

end Work.SSGRoute.PT.E1aFinBox
