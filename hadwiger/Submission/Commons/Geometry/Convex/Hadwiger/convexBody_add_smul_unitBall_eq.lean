import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Commons.Geometry.Convex.Hadwiger

theorem convexBody_add_smul_unitBall_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (K : ConvexBody V) {r : ℝ} (hr : 0 ≤ r) :
    ((K + r • (⟨Metric.closedBall (0:V) 1, convex_closedBall (0:V) 1, isCompact_closedBall (0:V) 1,
        Metric.nonempty_closedBall.mpr zero_le_one⟩ : ConvexBody V) : ConvexBody V) : Set V)
      = {x : V | ∃ k ∈ (K : Set V), dist x k ≤ r} := by
  ext x
  simp only [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_mk]
  rw [smul_unitClosedBall, Real.norm_of_nonneg hr]
  rw [Set.mem_add]
  constructor
  · rintro ⟨k, hk, y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact ⟨k, hk, by simpa [dist_eq_norm] using hy⟩
  · rintro ⟨k, hk, hk'⟩
    refine ⟨k, hk, x - k, ?_, by abel⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa [dist_eq_norm] using hk'

end Commons.Geometry.Convex.Hadwiger