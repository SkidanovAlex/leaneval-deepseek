import Mathlib

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- **Bounded chart values cannot accumulate at a point outside the chart's source.**  Let `c` be a
chart (an `OpenPartialHomeomorph`) such that every point with `‖c y‖ < 3R` lies in `c.source`, and
such that the ball of radius `3R` is contained in `c.target`.  Then for every `r < 3R` the set
`{y | ‖c y‖ ≤ r}` is closed.

Clean proof: `{y | ‖c y‖ ≤ r} = c.symm '' Metric.closedBall 0 r`.  Indeed, for `y` in the set,
`hsrc` gives `y ∈ c.source`, so `y = c.symm (c y)` and `c y ∈ closedBall 0 r`; conversely for
`w ∈ closedBall 0 r` we have `‖w‖ ≤ r < 3R`, hence `w ∈ Metric.ball 0 (3*R) ⊆ c.target`, so
`c (c.symm w) = w` and `c.symm w` is in the set.  Since `closedBall 0 r` is compact in finite
dimension and `c.symm` is continuous on `c.target` (an open set containing the closed ball), the set
is the image of a compact set under a continuous map, hence compact, hence closed (`T2Space M`). -/
theorem isClosed_setOf_norm_le {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {R r : ℝ} (hr : r < 3 * R)
    (hsrc : ∀ y : M, ‖c y‖ < 3 * R → y ∈ c.source)
    (htarget : Metric.ball 0 (3 * R) ⊆ c.target) :
    IsClosed {y : M | ‖c y‖ ≤ r} := by
  -- The closed ball of radius `r` sits inside the chart's target, since `r < 3R`.
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ c.target := by
    intro w hw
    apply htarget
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt (by simpa [dist_eq_norm] using hw) hr
  -- The set in question is the image of that closed ball under `c.symm`.
  have hset : {y : M | ‖c y‖ ≤ r} = c.symm '' Metric.closedBall 0 r := by
    ext y
    constructor
    · intro hy
      refine ⟨c y, ?_, c.left_inv (hsrc y (lt_of_le_of_lt hy hr))⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hy
    · rintro ⟨w, hw, rfl⟩
      have hwle : ‖w‖ ≤ r := by simpa [dist_eq_norm] using hw
      show ‖c (c.symm w)‖ ≤ r
      rw [c.right_inv (hball hw)]
      exact hwle
  rw [hset]
  -- A compact image under a continuous-on map is compact, hence closed in `M`.
  exact (IsCompact.image_of_continuousOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
    (c.continuousOn_symm.mono hball)).isClosed

end Work.Whitney
