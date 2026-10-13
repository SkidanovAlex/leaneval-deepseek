import Mathlib
import Submission.Work.WilC4aA.Defs

open Filter
open scoped Topology

namespace Work.WilC4aA

theorem analyticAt_exists_continuousOn {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ r > (0 : ℝ), ContinuousOn f (Set.Ioo (-r) r) := by
  have h : ∀ᶠ y in 𝓝 (0 : ℝ), ContinuousAt f y := hf.eventually_continuousAt
  rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hx' : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]; exact hx
  exact (hball hx').continuousWithinAt

end Work.WilC4aA
