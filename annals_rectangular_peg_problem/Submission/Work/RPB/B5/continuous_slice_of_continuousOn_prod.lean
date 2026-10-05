import Mathlib

namespace Work.RPB.B5

/-- Restricting a function that is continuous on the product `s ×ˢ u ×ˢ T`
(with domain `α × (β × γ)`) to a slice `{(x, (y, z)) | z ∈ T}` for fixed
`x ∈ s`, `y ∈ u` yields a function continuous on `T`. -/
theorem continuous_slice_of_continuousOn_prod {α β γ δ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ] {F : α × (β × γ) → δ}
    {s : Set α} {u : Set β} {T : Set γ} {x : α} {y : β} (hx : x ∈ s) (hy : y ∈ u)
    (hF : ContinuousOn F (s ×ˢ u ×ˢ T)) : ContinuousOn (fun z : γ => F (x, (y, z))) T := by
  have hg : Continuous fun z : γ => (x, (y, z)) := by continuity
  have hmaps : Set.MapsTo (fun z : γ => (x, (y, z))) T (s ×ˢ u ×ˢ T) := by
    intro z hz
    exact ⟨hx, hy, hz⟩
  exact hF.comp hg.continuousOn hmaps

end Work.RPB.B5
