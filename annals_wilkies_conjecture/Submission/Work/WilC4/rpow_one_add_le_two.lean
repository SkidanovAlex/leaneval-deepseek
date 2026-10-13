import Mathlib

namespace Work.WilC4

lemma rpow_one_add_le_two (u n : ℝ) (hu0 : 0 ≤ u) (hn : 0 ≤ n)
    (hnu : n * u ≤ Real.log 2 / 2) : (1 + u) ^ n ≤ 2 := by
  have h1u : 0 < 1 + u := by linarith
  rw [Real.rpow_le_iff_le_log h1u (by norm_num)]
  have hlog : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos h1u
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : n * Real.log (1 + u) ≤ n * u := mul_le_mul_of_nonneg_left hlog hn
  linarith

end Work.WilC4
