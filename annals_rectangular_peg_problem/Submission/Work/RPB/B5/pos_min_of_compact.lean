import Mathlib

namespace Work.RPB.B5

theorem pos_min_of_compact {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) (hne : s.Nonempty) (f : X → ℝ) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, 0 < f x) : ∃ η > 0, ∀ x ∈ s, η ≤ f x := by
  obtain ⟨x, hxs, hmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x, hpos x hxs, fun y hy => hmin hy⟩

end Work.RPB.B5
