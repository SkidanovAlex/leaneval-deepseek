import Mathlib

namespace Work.WilE2.WilE2Aux

/-- For a homeomorphism `e : α ≃ₜ β`, the image under `e` of the connected component of a
point `z` in a set `Y ⊆ α` is the connected component of `e z` in `e '' Y`. This is
`Homeomorph.image_connectedComponentIn` when `z ∈ Y`; when `z ∉ Y` both sides are empty. -/
lemma image_connectedComponentIn_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) (Y : Set α) (z : α) :
    e '' connectedComponentIn Y z = connectedComponentIn (e '' Y) (e z) := by
  by_cases hz : z ∈ Y
  · exact e.image_connectedComponentIn hz
  · rw [connectedComponentIn_eq_empty hz, Set.image_empty, connectedComponentIn_eq_empty]
    intro hmem
    rw [Set.mem_image] at hmem
    obtain ⟨y, hy, hyz⟩ := hmem
    exact hz (e.injective hyz ▸ hy)

theorem finite_range_componentIn_image_of_hits {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) {Y : Set α} {s : Finset α}
    (h : ∀ y ∈ Y, ∃ z ∈ s, connectedComponentIn Y y = connectedComponentIn Y z) :
    (Set.range (connectedComponentIn (e '' Y))).Finite := by
  classical
  -- The range is contained in the (finite) image of the components of the hits `e '' s`,
  -- together with the value `∅` taken outside `e '' Y`.
  refine ((Finset.finite_toSet (s.image fun z => connectedComponentIn (e '' Y) (e z))).union
      (Set.finite_singleton (∅ : Set β))).subset ?_
  rintro w ⟨b, rfl⟩
  by_cases hb : b ∈ e '' Y
  · -- `b = e y` with `y ∈ Y`; use the hitting hypothesis to replace `y` by some `z ∈ s`.
    obtain ⟨y, hyY, rfl⟩ := hb
    obtain ⟨z, hzs, hzy⟩ := h y hyY
    have hzy' : connectedComponentIn (e '' Y) (e y) = connectedComponentIn (e '' Y) (e z) := by
      rw [← image_connectedComponentIn_homeomorph e Y y,
          hzy, image_connectedComponentIn_homeomorph e Y z]
    exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z, hzs, hzy'.symm⟩))
  · -- Outside `e '' Y` the connected component in `e '' Y` is empty.
    exact Or.inr (by
      rw [Set.mem_singleton_iff]
      exact connectedComponentIn_eq_empty hb)

end Work.WilE2.WilE2Aux
