import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green

open MeasureTheory Metric

/-- The Newtonian kernel in `ℝ³` decays exactly like `(4π)⁻¹‖x‖⁻¹`; in particular
`‖newtonKernel x‖ ≤ (4π)⁻¹‖x‖ ^ (-1 : ℝ)` with equality for every `x`. -/
theorem norm_newtonKernel_eq (x : Work.FTS.PressureOn.R3) :
    ‖Work.FTS.PressureOn.newtonKernel x‖ = (4 * Real.pi)⁻¹ * ‖x‖ ^ (-1 : ℝ) := by
  rw [Work.FTS.PressureOn.newtonKernel, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (by positivity), Real.rpow_neg_one, mul_inv]

/-- The Newtonian kernel is measurable (indeed Borel measurable: it is `(4π‖x‖)⁻¹` and `inv` is
Borel measurable on `ℝ`, with the convention `0⁻¹ = 0`). -/
theorem measurable_newtonKernel : Measurable Work.FTS.PressureOn.newtonKernel := by
  have : Measurable fun x : Work.FTS.PressureOn.R3 => (4 * Real.pi * ‖x‖)⁻¹ :=
    Measurable.inv ((measurable_const (a := 4 * Real.pi)).mul continuous_norm.measurable)
  exact this

/-- **The Newtonian kernel is integrable on every ball centred at the origin of `ℝ³`.**  This is
the borderline `n = 3` case of the classical criterion: `‖x‖ ^ (-α)` is integrable near `0` in
dimension `d` exactly when `α < d`, and here `α = 1 < 3`.  The precise statement is the locally
integrable case `locallyIntegrable_of_norm_le_rpow` of the layer-cake formula. -/
theorem integrableOn_newtonKernel_ball (R : ℝ) :
    MeasureTheory.IntegrableOn (fun z : Work.FTS.PressureOn.R3 => Work.FTS.PressureOn.newtonKernel z)
      (Metric.ball (0 : Work.FTS.PressureOn.R3) R) := by
  have hfinrank : Module.finrank ℝ Work.FTS.PressureOn.R3 = 3 := by simp [Work.FTS.PressureOn.R3]
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume) (F := ℝ)
    (C := (4 * Real.pi)⁻¹) (α := 1) (r := R) ?_ ?_ ?_ ?_
  · rw [hfinrank]; norm_num
  · rw [hfinrank]; norm_num
  · filter_upwards
    intro x
    exact le_of_eq (norm_newtonKernel_eq x)
  · exact measurable_newtonKernel.aestronglyMeasurable

end Work.FTS.PressureOn.Green
