import Mathlib

namespace Work.Rep.Ore

/-- If `T : E → E` has dense range on a Hilbert space and `u : E → E` is bounded with
`‖u x‖ ≤ ‖T x‖` for all `x`, then `u` factors through `T`: there is a bounded `v` with
`v * T = u`.  (Use `LinearMap.extendOfNorm` and `LinearMap.extendOfNorm_eq` with constant `1`.) -/
theorem exists_continuousLinearMap_of_denseRange {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (T u : E →L[ℂ] E) (hT : DenseRange T) (h : ∀ x, ‖u x‖ ≤ ‖T x‖) : ∃ v : E →L[ℂ] E, v * T = u := by
  refine ⟨u.toLinearMap.extendOfNorm T.toLinearMap, ?_⟩
  ext x
  exact LinearMap.extendOfNorm_eq hT ⟨1, fun y => by rw [one_mul]; exact h y⟩ x

end Work.Rep.Ore
