import Mathlib
import Submission.Work.RPB.Port.Drive.WindingNumber
import Submission.Work.RPB.Port.Drive.winding_homotopy

/-!
# The winding number is locally constant in the point

The distance from a point `p` off a continuous closed curve `γ` to the (compact) image of `γ` is
positive, so `Work.RPB.Port.Drive.winding_homotopy` applies throughout a ball around `p`: the winding number
of `γ` about `p` is locally constant in `p`.
-/

namespace Work.RPB.Port.Drive

open scoped Topology

/-- **The winding number is locally constant in the point.**  There is a ball around `p` on which
`q ↦ winding γ hγ hq` is constant. -/
theorem exists_ball_winding_eq (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball p r, ∀ (hq : q ∉ Set.range γ),
      winding γ hγ hq = winding γ hγ hp := by
  have hclosed : IsClosed (Set.range γ) := (isCompact_range hγ).isClosed
  have hne : (Set.range γ).Nonempty := ⟨γ 0, Set.mem_range_self 0⟩
  have hpos : 0 < Metric.infDist p (Set.range γ) := (hclosed.notMem_iff_infDist_pos hne).mp hp
  refine ⟨Metric.infDist p (Set.range γ), hpos, fun q hq hq' => ?_⟩
  have hball : dist q p < Metric.infDist p (Set.range γ) := by
    simpa only [Metric.mem_ball, dist_comm] using hq
  refine winding_homotopy γ hγ hp hq' fun t => ?_
  have h1 : Metric.infDist p (Set.range γ) ≤ dist p (γ t) :=
    Metric.infDist_le_dist_of_mem (Set.mem_range_self t)
  rw [dist_comm (γ t) p]
  exact lt_of_lt_of_le hball h1

end Work.RPB.Port.Drive
