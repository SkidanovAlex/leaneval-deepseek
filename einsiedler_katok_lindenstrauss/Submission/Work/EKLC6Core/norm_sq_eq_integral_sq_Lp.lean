import Mathlib

namespace Work.EKLC6Core

open MeasureTheory

/-- The squared `L²` norm of a real `L²` function is the integral of its square. -/
theorem norm_sq_eq_integral_sq_Lp {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (g : MeasureTheory.Lp ℝ 2 μ) : ‖g‖ ^ 2 = ∫ x, ((g : X → ℝ) x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq g, L2.inner_def g g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show inner ℝ (g x) (g x) = (g x) ^ 2
  rw [Real.inner_apply]
  ring

end Work.EKLC6Core
