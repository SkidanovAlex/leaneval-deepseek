import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of a quadratic times a shifted Gaussian on `ℝ³`

For `a ≥ 0`, `b ≥ 0`, `c > 0` and any centre `w : ℝ³`, the function

`z ↦ (a + b‖z - w‖²) exp (-(c‖z - w‖²))`

is integrable on `ℝ³`.  This is the shifted (translation-invariant) form of the Gauss majorant
estimate `Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant`, and it is obtained from it by
composing with the translation `z ↦ z - w` (`MeasureTheory.Integrable.comp_sub_right`, valid
because Lebesgue measure on `ℝ³` is translation invariant).
-/

namespace Work.FTS.PressureOn.Auxiliary.gaussShift

theorem integrable_poly_exp_neg_normSq_sub (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (w : Work.FTS.PressureOn.R3) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (a + b * ‖z - w‖ ^ 2) * Real.exp (-(c * ‖z - w‖ ^ 2))) := by
  have h := (Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant a b c ha hb hc).comp_sub_right w
  simpa only [Pi.sub_apply] using h

end Work.FTS.PressureOn.Auxiliary.gaussShift
