import Mathlib

namespace Work.OROneRel

universe u

open Monoid.Coprod

theorem coprod_normalClosure {A B : Type u} [Group A] [Group B] (N : Subgroup A) (a : A) :
    (Monoid.Coprod.inl a : Monoid.Coprod A B) ∈
      Subgroup.normalClosure ((Monoid.Coprod.inl '' (N : Set A) : Set (Monoid.Coprod A B))) ↔
        a ∈ Subgroup.normalClosure N := by
  constructor
  · -- Forward direction: apply the retraction `fst : A ∗ B →* A`.
    intro h
    have hle : Subgroup.normalClosure (Monoid.Coprod.inl '' (N : Set A))
        ≤ (Subgroup.normalClosure N).comap (Monoid.Coprod.fst : Monoid.Coprod A B →* A) := by
      apply Subgroup.normalClosure_le_normal
      intro x hx
      rcases hx with ⟨n, hn, rfl⟩
      simpa using (Subgroup.subset_normalClosure hn : n ∈ Subgroup.normalClosure N)
    have := hle h
    simpa using this
  · -- Converse: `inl` maps the normal closure of `N` into the normal closure of `inl '' N`.
    intro h
    exact Subgroup.comap_normalClosure_image_ge (N : Set A)
      (Monoid.Coprod.inl : A →* Monoid.Coprod A B) h

end Work.OROneRel
