import Mathlib
import Submission.Work.FIArea7.ReflectAlg

namespace Work.FIArea7

/-- `reflSign` always takes one of the two values `±1`. -/
lemma reflSign_eq_one_or_neg_one (z1 z2 : GaussianInt) :
    reflSign z1 z2 = 1 ∨ reflSign z1 z2 = -1 := by
  unfold reflSign
  split_ifs <;> simp

theorem norm_reflSign_le_one (z1 z2 : GaussianInt) :
    ‖(Work.FIArea7.reflSign z1 z2 : ℂ)‖ ≤ 1 := by
  unfold Work.FIArea7.reflSign
  split_ifs <;> norm_num

end Work.FIArea7
