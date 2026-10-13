import Mathlib

namespace Work.WilE7

theorem imageSubsetConnectedComponentIn {α : Type*} {β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {s : Set α} (hs : IsPreconnected s)
    {f : α → β} (hf : ContinuousOn f s) {x : α} (hx : x ∈ s) {F : Set β}
    (hF : ∀ y ∈ s, f y ∈ F) : ∀ y ∈ s, f y ∈ connectedComponentIn F (f x) := by
  intro y hy
  -- `f '' s` is preconnected, as the continuous image of a preconnected set
  have himg : IsPreconnected (f '' s) := hs.image f hf
  -- and it lies in `F`, so it is contained in the component of `f x` in `F`
  have hsub : f '' s ⊆ connectedComponentIn F (f x) :=
    himg.subset_connectedComponentIn ⟨x, hx, rfl⟩
      (fun z hz => by obtain ⟨w, hw, rfl⟩ := hz; exact hF w hw)
  exact hsub ⟨y, hy, rfl⟩

end Work.WilE7
