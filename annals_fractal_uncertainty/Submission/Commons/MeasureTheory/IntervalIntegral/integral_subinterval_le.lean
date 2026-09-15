import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Real
open MeasureTheory Set

namespace Commons.MeasureTheory.IntervalIntegral

theorem integral_subinterval_le {f : ℝ → ℝ} {a b c d : ℝ}
    (hac : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hint : IntervalIntegrable f MeasureTheory.volume c d) (hf : ∀ t, 0 ≤ f t) :
    (∫ t in a..b, f t) ≤ (∫ t in c..d, f t) := by
  exact intervalIntegral.integral_mono_interval hac hab hbd (ae_of_all _ hf) hint

end Commons.MeasureTheory.IntervalIntegral