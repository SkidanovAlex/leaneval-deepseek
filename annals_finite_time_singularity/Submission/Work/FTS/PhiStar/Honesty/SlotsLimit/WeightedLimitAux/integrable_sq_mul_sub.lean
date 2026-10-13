import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Filter

theorem integrable_sq_mul_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ : α → ℝ} {w : α → ℝ}
    (h₁ : Integrable (fun x => (f₁ x * w x) ^ 2) μ)
    (h₂ : Integrable (fun x => (f₂ x * w x) ^ 2) μ)
    (hsm : AEStronglyMeasurable (fun x => (f₁ x - f₂ x) * w x) μ) :
    Integrable (fun x => ((f₁ x - f₂ x) * w x) ^ 2) μ := by
  -- Pointwise domination `((f₁ - f₂) w)² ≤ 2 (f₁ w)² + 2 (f₂ w)²`, from `(a - b)² ≤ 2a² + 2b²`
  -- (i.e. `(a + b)² ≥ 0`), together with the a.e. strong measurability of the difference.
  have hg : Integrable (fun x => 2 * (f₁ x * w x) ^ 2 + 2 * (f₂ x * w x) ^ 2) μ :=
    (h₁.const_mul 2).add (h₂.const_mul 2)
  refine hg.mono' (hsm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (f₁ x * w x + f₂ x * w x)]

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
