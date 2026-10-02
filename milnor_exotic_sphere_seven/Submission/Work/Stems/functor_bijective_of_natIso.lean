import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Stems

theorem functor_bijective_of_natIso {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (A : CategoryTheory.Functor C D) (B : CategoryTheory.Functor D C)
    (α : CategoryTheory.Iso (CategoryTheory.Functor.comp A B) (CategoryTheory.Functor.id C))
    (β : CategoryTheory.Iso (CategoryTheory.Functor.comp B A) (CategoryTheory.Functor.id D)) (c : C) :
    Function.Bijective (fun f : Quiver.Hom c c => A.map f) := by
  -- `A` admits a quasi-inverse `B`, so `A` is an equivalence of categories, hence fully faithful.
  have h := CategoryTheory.Functor.IsEquivalence.mk' B α.symm β
  exact ⟨fun f g hfg => h.faithful.map_injective hfg, fun g => h.full.map_surjective g⟩

end Work.Stems
