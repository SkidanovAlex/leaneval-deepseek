import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped Topology

namespace Commons.Analysis.Measure

/-- If `G : E → ℝ≥0∞` tends to `0` at `0` and `R i → 0`, then the supremum of `G` over the
closed ball of radius `R i` around `0` tends to `0`. -/
theorem tendsto_iSup_closedBall_nhds_zero {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} {l : Filter ι} {G : E → ENNReal} (hG : Filter.Tendsto G (nhds 0) (nhds 0))
    (R : ι → ℝ) (hR : Filter.Tendsto R l (nhds 0)) :
    Filter.Tendsto (fun i => ⨆ y ∈ Metric.closedBall (0 : E) (R i), G y) l (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hGε : {y : E | G y ≤ ε} ∈ 𝓝 (0 : E) := (ENNReal.tendsto_nhds_zero.1 hG) ε hε
  rw [Metric.mem_nhds_iff] at hGε
  obtain ⟨δ, hδpos, hδ⟩ := hGε
  have hRδ : ∀ᶠ i in l, R i ∈ Metric.ball (0 : ℝ) δ :=
    hR (Metric.ball_mem_nhds 0 hδpos)
  filter_upwards [hRδ] with i hi
  have hi' : |R i| < δ := by
    have := Metric.mem_ball.mp hi
    simpa [Real.dist_eq] using this
  refine iSup_le fun y => iSup_le fun hy => ?_
  exact hδ (Metric.mem_ball.mpr
    (lt_of_le_of_lt (le_trans (Metric.mem_closedBall.mp hy) (le_abs_self (R i))) hi'))

end Commons.Analysis.Measure