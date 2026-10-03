import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.LI

/-- Local indicability is inherited along injective homomorphisms: if `G` embeds into a locally
indicable group `H`, then `G` itself is locally indicable.

The point is that an injective `f : G →* H` carries a nontrivial finitely generated subgroup
`K ≤ G` to a nontrivial finitely generated subgroup `K.map f ≤ H`, and `K ≃* K.map f`; a
surjection `K.map f →* Multiplicative ℤ` therefore pulls back to one out of `K`. -/
theorem locallyIndicable_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : Group.LocallyIndicable H) : Group.LocallyIndicable G := by
  classical
  intro K hKfg hKne
  -- `K.map f` is finitely generated, being the image of a finitely generated subgroup.
  have hmapfg : (K.map f).FG := by
    obtain ⟨S, hS⟩ := Subgroup.isMulFG_iff.mp hKfg
    refine Subgroup.isMulFG_iff.mpr ⟨S.image f, ?_⟩
    rw [← hS, MonoidHom.map_closure, Finset.coe_image]
  -- and it is nontrivial because `f` is injective and `K ≠ ⊥`.
  have hmapne : K.map f ≠ ⊥ := fun hbot =>
    hKne ((Subgroup.map_eq_bot_iff_of_injective K hf).mp hbot)
  obtain ⟨g, hg⟩ := h (K.map f) hmapfg hmapne
  -- transport the surjection `K.map f →* Multiplicative ℤ` across `K ≃* K.map f`.
  exact ⟨g.comp (K.equivMapOfInjective f hf), hg.comp (K.equivMapOfInjective f hf).surjective⟩

end Work.ORLocInd.LI
