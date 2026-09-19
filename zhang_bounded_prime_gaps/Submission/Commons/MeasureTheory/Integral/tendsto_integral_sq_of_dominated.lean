import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory Filter
open scoped Topology

set_option linter.unusedVariables false in
/-- If `f n → g` pointwise a.e. and all `f n` are dominated by an `L²` function `b`, then the
integrals of the squares converge. -/
theorem tendsto_integral_sq_of_dominated {α : Type*} [MeasurableSpace α]
    {μ : _root_.MeasureTheory.Measure α}
    {f : ℕ → α → ℝ} {g b : α → ℝ}
    (hf : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (f n) μ)
    (hg : _root_.MeasureTheory.AEStronglyMeasurable g μ)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hbound : ∀ᵐ x ∂μ, ∀ n, |f n x| ≤ b x)
    (hb : _root_.MeasureTheory.Integrable (fun x => (b x) ^ 2) μ) :
    Tendsto (fun n => ∫ x, (f n x) ^ 2 ∂μ) atTop (𝓝 (∫ x, (g x) ^ 2 ∂μ)) := by
  refine _root_.MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => (b x) ^ 2) (fun n => (hf n).pow 2) hb ?_ ?_
  · intro n
    filter_upwards [hbound] with x hx
    have hbn : 0 ≤ b x := le_trans (abs_nonneg _) (hx 0)
    have hle : (f n x) ^ 2 ≤ (b x) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hbn]
      exact hx n
    change ‖(f n x) ^ 2‖ ≤ (b x) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f n x))]
    exact hle
  · filter_upwards [hconv] with x hx using hx.pow 2

end Commons.MeasureTheory.Integral