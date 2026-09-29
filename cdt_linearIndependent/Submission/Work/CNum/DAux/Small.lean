import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.SmallBox

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem small_ptOf_cusp : Small ptCuspA ∧ Small ptCuspB := by
  constructor <;> (unfold Small <;> decide +kernel)

theorem small_ptOf (k : ℕ) (hk : k ≤ 1024) : Small (ptOf k) := by
  unfold Small
  interval_cases k <;> decide +kernel

end Work.CNum
