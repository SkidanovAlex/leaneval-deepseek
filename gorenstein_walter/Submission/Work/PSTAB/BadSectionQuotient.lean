import Mathlib
import Submission.Work.PSTAB.Defs

set_option autoImplicit false

/-!
# `Work.PSTAB.BadSectionQuotient`

Sections of a quotient are sections: if `M` has no bad section
(`Work.PSTAB.NoBadSection M`), then neither does any quotient `M ⧸ C`.  Concretely, every
subgroup `Q` of `M ⧸ C` is isomorphic to the section `K ⧸ C` of `M` with
`K = π ⁻¹ Q`, so a noncyclic `2`-subgroup `Q` with a unique involution would already
exhibit a bad section of `M`.

The proof only needs the case `K = ⊤`: the projection restricted to `⊤` induces an
isomorphism `⊤ ⧸ ker f ≃* M ⧸ C`, and `Q` is transported back along it.
-/

namespace Work.PSTAB

theorem BadSectionQuotient {M : Type*} [Group M] (hM : Work.PSTAB.NoBadSection M)
    (C : Subgroup M) [C.Normal] (Q : Subgroup (M ⧸ C)) (hQ2 : IsPGroup 2 Q)
    (hnc : ¬ IsCyclic Q) (hu : ∃! z : Q, orderOf z = 2) : False := by
  -- the projection `⊤ ⧸ ker f ≃* M ⧸ C`, where `f` is the quotient map restricted to `⊤`
  let f : (⊤ : Subgroup M) →* M ⧸ C := (QuotientGroup.mk' C).comp (⊤ : Subgroup M).subtype
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  let e : ((⊤ : Subgroup M) ⧸ f.ker) ≃* (M ⧸ C) :=
    QuotientGroup.quotientKerEquivOfSurjective f hsurj
  -- pull `Q` back along `e`
  let Q' : Subgroup ((⊤ : Subgroup M) ⧸ f.ker) := Q.comap e
  have hmap : Q'.map e = Q := Subgroup.map_comap_eq_self_of_surjective e.surjective Q
  let eQ : ↥Q' ≃* ↥Q :=
    (Subgroup.equivMapOfInjective Q' e e.injective).trans (MulEquiv.subgroupCongr hmap)
  -- the three hypotheses transport across `eQ`
  have hQ2' : IsPGroup 2 Q' := hQ2.of_equiv eQ.symm
  have hnc' : ¬ IsCyclic Q' := by
    intro hc
    exact hnc (isCyclic_of_surjective eQ.toMonoidHom eQ.surjective)
  have hu' : ∃! z : Q', orderOf z = 2 := by
    obtain ⟨w, hw, hwu⟩ := hu
    refine ⟨eQ.symm w, ?_, ?_⟩
    · show orderOf (eQ.symm w) = 2
      rw [MulEquiv.orderOf_eq eQ.symm w]; exact hw
    · intro y hy
      have hy' : orderOf (eQ y) = 2 := by rw [MulEquiv.orderOf_eq eQ y]; exact hy
      have h2 : eQ y = w := hwu (eQ y) hy'
      rw [← MulEquiv.symm_apply_apply eQ y, h2]
  exact hM ⊤ f.ker Q' hQ2' hnc' hu'

end Work.PSTAB
