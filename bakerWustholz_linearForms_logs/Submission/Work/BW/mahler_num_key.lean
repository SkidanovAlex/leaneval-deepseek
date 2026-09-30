import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A convenient numeric upper bound for `log 2` (weaker than `Real.log_two_lt_d9`,
but all the target inequality needs). -/
theorem log_two_lt_seven_tenths : Real.log 2 < (7/10 : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

theorem mahler_num_key {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    (Real.log 2 / 2 + 1) * n * L - 1/5
      < ((54/5) * n * L - 1) * (1/5 - 5 * 0.6931471808 / 48) := by
  have hlog : Real.log 2 < (7/10 : ℝ) := log_two_lt_seven_tenths
  have hnp : 0 < n * L := mul_pos hn hL
  nlinarith [hnp, hlog]

end Work.BW
