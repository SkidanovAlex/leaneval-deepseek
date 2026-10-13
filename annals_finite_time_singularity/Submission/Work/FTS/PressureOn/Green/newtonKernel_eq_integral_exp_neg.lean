import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green

/-- **The Newtonian kernel as a one-dimensional Gaussian integral.**

`newtonKernel z = (4π‖z‖)⁻¹`, and the half-line Gaussian integral with parameter `b = ‖z‖²` is
`∫_0^∞ exp(-s²‖z‖²) ds = √(π/‖z‖²)/2 = √π/(2‖z‖)`; multiplying by `(2π√π)⁻¹` gives
`1/(4π‖z‖)`.  The case `z = 0` is excluded, as it must be (the integral is then divergent). -/
theorem newtonKernel_eq_integral_exp_neg (z : Work.FTS.PressureOn.R3) (hz : z ≠ 0) :
    Work.FTS.PressureOn.newtonKernel z = (2 * Real.pi * Real.sqrt Real.pi)⁻¹ *
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s ^ 2 * ‖z‖ ^ 2)) := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hI : (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(s ^ 2 * ‖z‖ ^ 2)))
      = Real.sqrt (Real.pi / ‖z‖ ^ 2) / 2 := by
    rw [← integral_gaussian_Ioi (‖z‖ ^ 2)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    congr 1
    ring
  rw [Work.FTS.PressureOn.newtonKernel, hI,
    Real.sqrt_div Real.pi_pos.le (‖z‖ ^ 2), Real.sqrt_sq hnorm.le]
  field_simp
  ring

end Work.FTS.PressureOn.Green
