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

theorem integrable_mul_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f h w : α → ℝ}
    (hwpos : ∀ᵐ x ∂μ, 0 < w x)
    (hfm : AEStronglyMeasurable f μ) (hhm : AEStronglyMeasurable h μ)
    (hf2 : Integrable (fun x => (f x * w x) ^ 2) μ)
    (hh2 : Integrable (fun x => (h x / w x) ^ 2) μ) :
    Integrable (fun x => f x * h x) μ := by
  have amgm : ∀ a b : ℝ, |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    intro a b
    rw [abs_mul]
    have h1 := two_mul_le_add_sq |a| |b|
    rw [sq_abs, sq_abs] at h1
    linarith
  have hgint : Integrable (fun x => ((f x * w x) ^ 2 + (h x / w x) ^ 2) / 2) μ :=
    (hf2.add hh2).div_const 2
  refine hgint.mono' (hfm.mul hhm) ?_
  filter_upwards [hwpos] with x hx
  rw [Real.norm_eq_abs]
  have hwx : w x ≠ 0 := ne_of_gt hx
  have heq : f x * h x = (f x * w x) * (h x / w x) := by field_simp
  rw [heq]
  exact amgm _ _

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
