import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Measure.FinFunction.eucl_ball_exterior_pow_six
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `‖p‖⁻⁶` on the exterior of a ball in ℝ³

For every `R > 0`, the function `p ↦ (‖p‖ ^ 6)⁻¹` is integrable (w.r.t. Lebesgue
measure on `EuclideanSpace ℝ (Fin 3)`) on the exterior `{p | R ≤ ‖p‖}`.

The value of the (Bochner) integral over this exterior was already computed in
`Commons.Measure.FinFunction.eucl_ball_exterior_pow_six` to be the finite
positive number `(4 / 3) * π * (R³)⁻¹`.  A Bochner integral that is non-zero is
necessarily the integral of an integrable function
(`MeasureTheory.Integrable.of_integral_ne_zero`), and integrability w.r.t. the
restricted measure `volume.restrict s` is exactly `IntegrableOn` on `s`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Commons.Measure.FinFunction

theorem integrableOn_exterior_inv_pow_six (R : ℝ) (hR : 0 < R) :
    MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ 6)⁻¹)
      {p : EuclideanSpace ℝ (Fin 3) | R ≤ ‖p‖} := by
  have hval := eucl_ball_exterior_pow_six R hR
  have hne : (∫ p : EuclideanSpace ℝ (Fin 3) in {p : EuclideanSpace ℝ (Fin 3) | R ≤ ‖p‖},
      (‖p‖ ^ 6)⁻¹) ≠ 0 := by
    rw [hval]
    positivity
  change MeasureTheory.Integrable
    (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ 6)⁻¹)
    (volume.restrict {p : EuclideanSpace ℝ (Fin 3) | R ≤ ‖p‖})
  exact MeasureTheory.Integrable.of_integral_ne_zero hne

end Commons.Measure.FinFunction
