import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem integrable_sqrt_mul_sqrt (μ : MeasureTheory.Measure ℝ) (A B : ℝ → ℝ)
    (hA : MeasureTheory.Integrable A μ) (hB : MeasureTheory.Integrable B μ)
    (hAn : ∀ x, 0 ≤ A x) (hBn : ∀ x, 0 ≤ B x) :
    MeasureTheory.Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x)) μ := by
  -- Dominate `√A * √B` by the integrable function `(A + B) / 2` (AM-GM).
  have hsum : MeasureTheory.Integrable (fun x => (A x + B x) / 2) μ :=
    (hA.add hB).div_const 2
  refine hsum.mono' ?_ ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable)
  · filter_upwards with x
    have hA0 := hAn x
    have hB0 := hBn x
    have hsq : (0 : ℝ) ≤ (Real.sqrt (A x) - Real.sqrt (B x)) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]

end Work.Coercivity
