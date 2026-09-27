import Mathlib
import Submission.Work.EQ.FatouDefs

namespace Work.EQ.Fatou

theorem pkS_nonneg (r s : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (hs : s ∈ Set.Icc 0 Real.pi) :
    0 ≤ Work.EQ.pkS r s := by
  unfold Work.EQ.pkS
  apply div_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact hr
      · have h1 : 0 ≤ 1 - r := by linarith
        have h2 : 0 ≤ 1 + r := by linarith
        nlinarith [mul_nonneg h1 h2]
    · exact Real.sin_nonneg_of_mem_Icc hs
  · exact sq_nonneg _

end Work.EQ.Fatou
