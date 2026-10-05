import Mathlib
import Submission.Work.RPB.B1.PolarDefs
import Submission.Work.RPB.B1.region_mem_ball

namespace Work.RPB.B1

/-- Membership of the polar point `r e^{iφ}` in the disc `ball a R`, with `‖a‖ < R` and `r > 0`,
phrased in terms of the radial extent `radial a R φ` of the disc in direction `φ`. -/
theorem polar_region (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) (r φ : ℝ) (hr : 0 < r) :
    ‖(Complex.polarCoord.symm (r, φ) : ℂ) - a‖ < R ↔ r < radial a R φ := by
  have h := region_mem_ball a hR (r, φ) hr
  rw [Metric.mem_ball, dist_eq_norm] at h
  rw [radial]
  exact h

end Work.RPB.B1
