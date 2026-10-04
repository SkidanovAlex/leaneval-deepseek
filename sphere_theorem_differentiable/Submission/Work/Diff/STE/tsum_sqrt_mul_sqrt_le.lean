import Mathlib
import Submission.Work.Diff.STE.fill.tsum_sqrt_mul_sqrt_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

theorem tsum_sqrt_mul_sqrt_le {α : Type*} {A B : α → ℝ}
    (hA : Summable A) (hB : Summable B) (hA0 : ∀ a, 0 ≤ A a) (hB0 : ∀ a, 0 ≤ B a) :
    (∑' a, Real.sqrt (A a) * Real.sqrt (B a)) ≤
      Real.sqrt (∑' a, A a) * Real.sqrt (∑' a, B a) :=
  Work.Diff.STE.fill.tsum_sqrt_mul_sqrt_le hA hB hA0 hB0

end Work.Diff.STE
