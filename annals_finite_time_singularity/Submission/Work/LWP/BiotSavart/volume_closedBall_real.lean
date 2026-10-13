import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

/-- The Lebesgue volume of the closed ball of radius `R` about the origin in `ℝ³` is
`R³ · (4π/3)`.  `MeasureTheory.Measure.real` is `ENNReal.toReal` of the measure of the set,
and `R ≥ 0` makes `ENNReal.ofReal R`'s `toReal` come back to `R`. -/
theorem volume_closedBall_real (R : ℝ) (hR : 0 ≤ R) :
    MeasureTheory.Measure.real MeasureTheory.volume (Metric.closedBall (0 : R3) R)
      = R ^ 3 * (Real.pi * 4 / 3) := by
  rw [MeasureTheory.Measure.real, EuclideanSpace.volume_closedBall_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]

end Work.LWP.BiotSavart
