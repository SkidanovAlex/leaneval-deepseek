import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst.AngGap

/-- The square of `sin (2 * ·)` integrated over `[θ, π/2]` equals its integral over
`[0, π/2 - θ]`: substitute `s ↦ π/2 - s` and use `sin (π - x) = sin x`. -/
theorem int_sinSq_shift (θ : ℝ) :
    ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 = ∫ t in (0 : ℝ)..(π / 2 - θ), (Real.sin (2 * t)) ^ 2 := by
  have key : (∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2)
      = ∫ s in θ..(π / 2), (Real.sin (2 * (π / 2 - s))) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only []
    rw [show 2 * (π / 2 - s) = π - 2 * s by ring, Real.sin_pi_sub]
  rw [key, intervalIntegral.integral_comp_sub_left (fun x : ℝ => (Real.sin (2 * x)) ^ 2) (π / 2)]
  norm_num

end Work.FTS.EllipticEst.AngGap
