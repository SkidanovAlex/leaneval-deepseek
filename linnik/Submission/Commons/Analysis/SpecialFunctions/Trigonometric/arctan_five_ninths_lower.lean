import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.arctan_ge_taylor8

namespace Commons.Analysis.SpecialFunctions.Trigonometric

theorem arctan_five_ninths_lower : (5070/10000 : ℝ) ≤ Real.arctan (5/9) := by
  have h := arctan_ge_taylor8 (5/9) (by norm_num)
  have h2 : (5070/10000 : ℝ) ≤
      (5/9 : ℝ) - (5/9)^3/3 + (5/9)^5/5 - (5/9)^7/7 + (5/9)^9/9 - (5/9)^11/11
        + (5/9)^13/13 - (5/9)^15/15 := by
    norm_num
  linarith

end Commons.Analysis.SpecialFunctions.Trigonometric
