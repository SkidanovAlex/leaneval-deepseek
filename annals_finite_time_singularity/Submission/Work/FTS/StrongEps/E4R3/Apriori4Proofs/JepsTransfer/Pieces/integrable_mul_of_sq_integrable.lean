import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

theorem integrable_mul_of_sq_integrable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hfi : MeasureTheory.Integrable (fun y => f y ^ 2) μ)
    (hgi : MeasureTheory.Integrable (fun y => g y ^ 2) μ) :
    MeasureTheory.Integrable (fun y => f y * g y) μ := by
  -- Cauchy--Schwarz: `‖f y * g y‖ ≤ f y ^ 2 + g y ^ 2` pointwise, and the right-hand
  -- side is integrable by hypothesis.
  have hsum : MeasureTheory.Integrable (fun y => f y ^ 2 + g y ^ 2) μ := hfi.add hgi
  refine hsum.mono' ((hfm.mul hgm).aestronglyMeasurable) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul, ← sq_abs (f y), ← sq_abs (g y)]
  nlinarith [two_mul_le_add_sq (|f y|) (|g y|), abs_nonneg (f y), abs_nonneg (g y)]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
