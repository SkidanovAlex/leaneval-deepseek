import Mathlib

namespace Work.WilE7.CoreStep

theorem sign_const_of_isPreconnected {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsPreconnected C) {f : X → ℝ} (hf : ContinuousOn f C) (hne : ∀ x ∈ C, f x ≠ 0) {x₀ y : X} (hx₀ : x₀ ∈ C) (hy : y ∈ C) : (0 < f y ↔ 0 < f x₀) := by
  -- `f` is continuous on the preconnected set `C` and never vanishes there,
  -- so its image lies entirely in `Ioi 0` or entirely in `Iio 0`.
  rcases hC.mapsTo_Ioi_or_Iio (b := 0) hf hne with h | h
  · -- all values are positive
    exact ⟨fun _ => h hx₀, fun _ => h hy⟩
  · -- all values are negative
    exact ⟨fun h' => absurd h' (not_lt.mpr (le_of_lt (h hy))),
           fun h' => absurd h' (not_lt.mpr (le_of_lt (h hx₀)))⟩

end Work.WilE7.CoreStep
