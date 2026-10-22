import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits in
/-- Transport of a colimit cofan along an isomorphism of cofans which is only defined
up to a reindexing equivalence `e` of the index types.

If `d` is a colimit cofan for `P : α → C`, and `d'` is a cofan for `Q' : β → C` which is
identified with `d` through an equivalence `e : α ≃ β`, isomorphisms `θ a : P a ≅ Q' (e a)`
and an isomorphism `ψ : d.pt ≅ d'.pt` satisfying the compatibility
`d.inj a ≫ ψ.hom = (θ a).hom ≫ d'.inj (e a)`, then `d'` is a colimit cofan as well. -/
theorem isColimit_of_equiv_index {C : Type*} [Category C] {α β : Type*} {P : α → C} {Q' : β → C}
    (d : Cofan P) (d' : Cofan Q') (e : α ≃ β) (θ : ∀ a, P a ≅ Q' (e a)) (ψ : d.pt ≅ d'.pt)
    (h : ∀ a, d.inj a ≫ ψ.hom = (θ a).hom ≫ d'.inj (e a)) (hd : IsColimit d) :
    Nonempty (IsColimit d') := by
  refine ⟨IsColimit.mk (fun s => ψ.inv ≫
    hd.desc (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a))))) ?_ ?_⟩
  · intro s b
    obtain ⟨b⟩ := b
    -- For every `a : α` the candidate lift of `s` over `d'` restricts correctly at `e a`.
    have key : ∀ a : α, d'.ι.app (Discrete.mk (e a)) ≫ (ψ.inv ≫
        hd.desc (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a)))))
        = s.ι.app (Discrete.mk (e a)) := by
      intro a
      have hA : d.ι.app (Discrete.mk a) ≫ ψ.hom
          = (θ a).hom ≫ d'.ι.app (Discrete.mk (e a)) := h a
      have h2 : d'.ι.app (Discrete.mk (e a)) ≫ ψ.inv
          = (θ a).inv ≫ d.ι.app (Discrete.mk a) := by
        have h1 : d'.ι.app (Discrete.mk (e a))
            = (θ a).inv ≫ d.ι.app (Discrete.mk a) ≫ ψ.hom := by
          rw [hA, Iso.inv_hom_id_assoc]
        rw [h1]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hfac : d.ι.app (Discrete.mk a) ≫
          hd.desc (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a))))
          = (θ a).hom ≫ s.ι.app (Discrete.mk (e a)) :=
        hd.fac (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a))))
          (Discrete.mk a)
      rw [← Category.assoc, h2, Category.assoc, hfac, Iso.inv_hom_id_assoc]
    have hb := key (e.symm b)
    rw [Equiv.apply_symm_apply e b] at hb
    exact hb
  · intro s m hm
    have hm' : ∀ a : α, d'.ι.app (Discrete.mk (e a)) ≫ m = s.ι.app (Discrete.mk (e a)) :=
      fun a => hm (Discrete.mk (e a))
    -- `ψ.hom ≫ m` is the lift of `s` over `d`.
    have key : ∀ j : Discrete α, d.ι.app j ≫ (ψ.hom ≫ m)
        = (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a)))).ι.app j := by
      intro j
      obtain ⟨a⟩ := j
      have hA : d.ι.app (Discrete.mk a) ≫ ψ.hom
          = (θ a).hom ≫ d'.ι.app (Discrete.mk (e a)) := h a
      show d.ι.app (Discrete.mk a) ≫ (ψ.hom ≫ m)
        = (θ a).hom ≫ s.ι.app (Discrete.mk (e a))
      rw [← Category.assoc, hA, Category.assoc, hm' a]
    have huniq := hd.uniq (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a))))
      (ψ.hom ≫ m) key
    show m = ψ.inv ≫
      hd.desc (Cofan.mk s.pt (fun a => (θ a).hom ≫ s.ι.app (Discrete.mk (e a))))
    rw [← huniq]
    exact (Iso.inv_hom_id_assoc ψ m).symm

end Work.ANALYTIC
