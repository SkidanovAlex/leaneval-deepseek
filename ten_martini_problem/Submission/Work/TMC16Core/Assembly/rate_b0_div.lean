import Mathlib

namespace Work.TMC16Core.Assembly

/-- For any real `b₀`, the quantity `b₀ / (4 qn - 2)` tends to `0` as `qn → ∞`. -/
theorem rate_b0_div (b₀ : ℝ) : Filter.Tendsto (fun qn : ℝ => b₀ / (4 * qn - 2)) Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.const_div_atTop ?_ b₀
  have h : Filter.Tendsto (fun n : ℝ => 4 * n) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have h2 : Filter.Tendsto (fun n : ℝ => 4 * n - 2) Filter.atTop Filter.atTop := by
    simpa only [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right Filter.atTop (-2) h
  exact h2

end Work.TMC16Core.Assembly
