import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory

theorem ext_iso_subsingleton {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt C] {X Y Z : C} (e : X ≅ Y) (n : ℕ) :
    Subsingleton (CategoryTheory.Abelian.Ext X Z n) ↔
      Subsingleton (CategoryTheory.Abelian.Ext Y Z n) := by
  -- `Ext (-) Z n` is a functor in the first variable, so the isomorphism `e` induces
  -- an isomorphism of abelian groups `Ext Y Z n ≅ Ext X Z n`.
  have f : CategoryTheory.Abelian.Ext Y Z n ≃ CategoryTheory.Abelian.Ext X Z n :=
    (((CategoryTheory.Abelian.extFunctor (C := C) n).mapIso e.op).app Z)
      |>.addCommGroupIsoToAddEquiv.toEquiv
  constructor
  · intro h
    exact ⟨fun a b => f.injective (h.elim (f a) (f b))⟩
  · intro h
    exact ⟨fun a b => f.symm.injective (h.elim (f.symm a) (f.symm b))⟩

end Work.SSGRoute.ExtChain
