import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-- **The spherical-coordinate (radial) integral formula in `ℝ³`.**

For an arbitrary `g : ℝ → ℝ`, the integral over `ℝ³` of the radially symmetric function
`x ↦ g ‖x‖` equals `4π ∫_{(0,∞)} r² g r dr`.

No integrability hypothesis is needed: both sides are Bochner integrals with the
`integral_undef = 0` convention, and the two integrability conditions coincide.  The general
change-of-variables statement behind this (for an arbitrary additive Haar measure on a
finite-dimensional real normed space) is `MeasureTheory.integral_fun_norm_addHaar`; specialising
it to `R3 = EuclideanSpace ℝ (Fin 3)`, where `finrank ℝ R3 = 3` and the unit ball has volume
`4π/3`, gives the stated identity. -/
theorem integral_radial (g : ℝ → ℝ) :
    ∫ x : R3, g ‖x‖ = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r := by
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure R3)) (F := ℝ) g]
  have hfr : Module.finrank ℝ R3 = 3 := by simp
  have hvol : (volume : Measure R3).real (Metric.ball 0 1) = 4 * Real.pi / 3 := by
    rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hfr, hvol]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

end Work.FTS.PressureOn.PoissonAux
