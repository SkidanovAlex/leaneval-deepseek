import Mathlib

namespace Work.HornCov

/-- A continuous map `g` that admits a continuous left inverse `f` (`f (g y) = y`) has
closed range, provided the target `X` is Hausdorff. -/
theorem isClosed_range_of_continuous_section {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {f : X → Y} {g : Y → X} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y, f (g y) = y) : IsClosed (Set.range g) := by
  -- `range g` is exactly the equalizer of `g ∘ f` and the identity on `X`.
  have hset : Set.range g = {x : X | g (f x) = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show g (f (g y)) = g y
      rw [h y]
    · intro hx
      exact ⟨f x, hx⟩
  rw [hset]
  exact isClosed_eq (hg.comp hf) continuous_id

end Work.HornCov
