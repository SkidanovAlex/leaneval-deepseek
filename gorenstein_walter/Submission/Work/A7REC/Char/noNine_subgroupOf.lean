import Mathlib

namespace Work.A7REC.Char

theorem noNine_subgroupOf {G : Type*} [Group G] {U H : Subgroup G} (hUH : U ≤ H)
    (h : ∀ P : Subgroup G, Nat.card P = 9 → ∃ p ∈ P, p ≠ 1 ∧ ∀ g : G, ∀ u ∈ U, g * u * g⁻¹ ≠ p) :
    ∀ P : Subgroup ↥H, Nat.card P = 9 →
      ∃ p ∈ P, p ≠ 1 ∧ ∀ g : ↥H, ∀ u ∈ U.subgroupOf H, g * u * g⁻¹ ≠ p := by
  intro P hP
  -- view `P ≤ ↥H` as a subgroup of `G` of the same order, via the inclusion `↥H → G`
  have hcard : Nat.card (Subgroup.map H.subtype P) = 9 := by
    rw [← Nat.card_congr
      (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).toEquiv, hP]
  obtain ⟨p, hp, hpne, hconj⟩ := h (Subgroup.map H.subtype P) hcard
  -- lift `p` back to an element of `↥H` lying in `P`
  rw [Subgroup.mem_map] at hp
  obtain ⟨x, hxP, hxp⟩ := hp
  refine ⟨x, hxP, ?_, ?_⟩
  · -- `x ≠ 1` because its image `p` is `≠ 1`
    intro hx1
    exact hpne (by rw [← hxp, hx1]; rfl)
  · -- conjugation inside `↥H` is conjugation inside `G`, so `hconj` applies
    intro g u hu hgu
    refine hconj (g : G) (u : G) ((Subgroup.mem_subgroupOf).mp hu) ?_
    rw [← hxp]
    exact congrArg Subtype.val hgu

end Work.A7REC.Char
