import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs
import Submission.Work.BMF.liouville.vk_large_lam_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

theorem vk_easy_numeric_key (N lam : ℝ) (hlam : 13/5 ≤ lam)
    (hlogN : 1000 * lam ^ 2 ≤ Real.log N) :
    (2 * (Work.BMF.liouville.dK lam : ℝ) + 1) * Real.log 2 ≤ (1/5) * Real.log N := by
  obtain ⟨_, _, _, _, _, _, _, hK5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    vk_large_lam_bounds lam hlam
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9; linarith
  have hlog2pos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK5' : 2 * (dK lam : ℝ) + 1 ≤ 10 * lam + 5 := by linarith
  have hl255 : (0:ℝ) ≤ 10 * lam + 5 := by linarith
  have hquad : 10 * lam + 5 ≤ 200 * lam ^ 2 := by nlinarith [hlam]
  have hmul1 : (2 * (dK lam : ℝ) + 1) * Real.log 2 ≤ (10 * lam + 5) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hK5' hlog2pos
  have hmul2 : (10 * lam + 5) * Real.log 2 ≤ (10 * lam + 5) * 1 :=
    mul_le_mul_of_nonneg_left hlog2 hl255
  have h1 : (2 * (dK lam : ℝ) + 1) * Real.log 2 ≤ 10 * lam + 5 := by
    linarith [hmul1, hmul2]
  have h2 : (200:ℝ) * lam ^ 2 ≤ (1/5) * Real.log N := by
    have := mul_le_mul_of_nonneg_left hlogN (by norm_num : (0:ℝ) ≤ 1/5)
    linarith
  have h3 : (200:ℝ) * lam ^ 2 = (1/5) * (1000 * lam ^ 2) := by ring
  linarith [h1, hquad, h2, h3]

end Work.BMF.liouville
