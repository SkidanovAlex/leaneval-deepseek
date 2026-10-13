import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CSTools

/-- The interval integral is additive over adjacent intervals, hence the triangle
inequality holds for the absolute values.  No integrability hypothesis is needed: if
`f` is not interval-integrable on `[a, b]`, the left-hand side is `0` by
`intervalIntegral.integral_undef`, and if it is, the two pieces are integrable by
monotonicity of `IntegrableOn` (each `Ioc` is contained in `Ioc a b`). -/
theorem abs_intervalIntegral_le_abs_add {f : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    |∫ t in a..b, f t| ≤ |∫ t in a..m, f t| + |∫ t in m..b, f t| := by
  by_cases h : IntervalIntegrable f MeasureTheory.volume a b
  · have hab : a ≤ b := ham.trans hmb
    have hIoc : MeasureTheory.IntegrableOn f (Set.Ioc a b) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 h
    have h1 : IntervalIntegrable f MeasureTheory.volume a m :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ham).2
        (hIoc.mono_set (Set.Ioc_subset_Ioc_right hmb))
    have h2 : IntervalIntegrable f MeasureTheory.volume m b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hmb).2
        (hIoc.mono_set (Set.Ioc_subset_Ioc_left ham))
    have heq : (∫ t in a..m, f t) + (∫ t in m..b, f t) = ∫ t in a..b, f t :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    rw [← heq]
    exact abs_add_le _ _
  · rw [intervalIntegral.integral_undef h, abs_zero]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)

end Work.FTS.PhiStar.Honesty.CSTools
