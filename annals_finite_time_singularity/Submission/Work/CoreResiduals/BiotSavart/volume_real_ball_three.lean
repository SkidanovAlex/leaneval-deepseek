import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- The Lebesgue measure (as a real number) of an open ball in `ℝ³`:
`|B(x,r)| = (4π/3) r³`, in the form `r³ * (π * 4 / 3)`.

Immediate from the explicit three-dimensional volume formula
`EuclideanSpace.volume_ball_fin_three`, which gives
`volume (B(x,r)) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (π * 4 / 3)`. -/
theorem volume_real_ball_three {x : Work.LWP.R3} {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.volume.real (Metric.ball x r) = r ^ 3 * (Real.pi * 4 / 3) := by
  rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity)]

end Work.CoreResiduals.BiotSavart
