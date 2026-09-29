import Mathlib
import Submission.Work.TMComp.RotBasics.Defs

namespace Work.TMC13

open Work.TMComp.RotBasics

/-- The point `vc (-2t)` lies on the unit circle, so the perturbation `r * vc (-2t)` has
norm `‖r‖ < 1`; consequently `1 + r * vc (-2t)` has positive real part and avoids the
negative real axis, i.e. lies in the slit plane. -/
theorem ref_perturb_slitPlane (r : ℂ) (hr : ‖r‖ < 1) (t : ℝ) :
    1 + r * Work.TMComp.RotBasics.vc (-2 * t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hnorm : ‖r * vc (-2 * t)‖ = ‖r‖ := by
    rw [Complex.norm_mul, vc_norm, mul_one]
  have hre : -‖r‖ ≤ (r * vc (-2 * t)).re := by
    have h := Complex.abs_re_le_norm (r * vc (-2 * t))
    rw [hnorm] at h
    have h2 := neg_abs_le (r * vc (-2 * t)).re
    linarith
  rw [Complex.add_re, Complex.one_re]
  linarith

end Work.TMC13
