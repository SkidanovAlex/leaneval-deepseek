import Mathlib
import Submission.Work.Smooth.Jordan.Separation

namespace Work.Smooth.Jordan

/-- The trace of a plane curve is compact, hence bounded, and the *inside* `V` of a plane
separation is bounded; a point of sufficiently large norm is therefore outside both, so outside
`c.trace`, and hence lies in the unbounded side `U`. -/
theorem plane_separation_unbounded {c : PlaneCurve} (h : PlaneSeparation c) : ∀ R : ℝ, ∃ x ∈ h.U, R ≤ ‖x‖ := by
  intro R
  obtain ⟨r, hrV⟩ := h.bounded_V.subset_closedBall (0 : ℂ)
  obtain ⟨s, hs⟩ := c.isCompact_trace.isBounded.subset_closedBall (0 : ℂ)
  set M : ℝ := max (max r s) R + 1 with hM
  have hMr : r < M := by rw [hM]; linarith [le_max_left r s, le_max_left (max r s) R]
  have hMs : s < M := by rw [hM]; linarith [le_max_right r s, le_max_left (max r s) R]
  have hMR : R < M := by rw [hM]; linarith [le_max_right (max r s) R]
  have hnorm : ‖((M : ℝ) : ℂ)‖ = |M| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hx_not_trace : ((M : ℝ) : ℂ) ∉ c.trace := by
    intro hmem
    have h1 := hs hmem
    rw [Metric.mem_closedBall, dist_zero_right, hnorm] at h1
    linarith [lt_of_lt_of_le hMs (le_abs_self M)]
  have hx_not_V : ((M : ℝ) : ℂ) ∉ h.V := by
    intro hmem
    have h1 := hrV hmem
    rw [Metric.mem_closedBall, dist_zero_right, hnorm] at h1
    linarith [lt_of_lt_of_le hMr (le_abs_self M)]
  refine ⟨((M : ℝ) : ℂ), ?_, ?_⟩
  · rw [PlaneSeparation.mem_iff h hx_not_trace]; exact hx_not_V
  · rw [hnorm]; linarith [lt_of_lt_of_le hMR (le_abs_self M)]

end Work.Smooth.Jordan
