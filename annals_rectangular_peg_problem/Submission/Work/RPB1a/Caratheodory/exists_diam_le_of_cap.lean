import Mathlib

namespace Work.RPB1a.Caratheodory

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- A sequence of shrinking caps whose images have diameter tending to zero can be replaced by a
single cap whose image has diameter at most any prescribed positive tolerance. -/
theorem exists_diam_le_of_cap {Φ : ℂ → ℂ} {ζ : ℂ}
    (hcap : ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n < 1) ∧
      Tendsto r atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => Metric.diam (Φ '' (ball ζ (r n) ∩ ball 0 1))) atTop (𝓝 (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ Metric.diam (Φ '' (ball ζ r ∩ ball 0 1)) ≤ ε := by
  obtain ⟨r, hr, _hr0, hdiam⟩ := hcap
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hdiam) ε hε
  refine ⟨r N, (hr N).1, le_of_lt ?_⟩
  have h := hN N le_rfl
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg] at h

end Work.RPB1a.Caratheodory
