import Mathlib
import Submission.Work.EQ.FatouDefs

namespace Work.EQ.Fatou

/-- The angle Poisson kernel `pk r ψ = (1 - r²)/(1 - 2 r cos ψ + r²)` is nonnegative on the
unit disc (`0 ≤ r < 1`): the numerator is nonnegative and the denominator is positive. -/
theorem pk_nonneg (r ψ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : 0 ≤ Work.EQ.pk r ψ := by
  unfold Work.EQ.pk
  apply div_nonneg
  · nlinarith
  · have h := Real.cos_le_one ψ
    nlinarith

end Work.EQ.Fatou
