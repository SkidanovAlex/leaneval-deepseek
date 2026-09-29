import Mathlib
import Submission.Work.C17I.defs
import Submission.Work.C17.lc_defs

namespace Work.C17I

/-- Numerically `‖sw p₀‖ = ‖p₀/(p₀−1)‖ ≤ 1/2`, while the cusp hypothesis says
`xsOf m n ≥ 1 − 1/100000 > 1/2`. -/
theorem sw_p0_lt (m n : ℕ) (hx1 : 1 - 1 / 100000 ≤ Work.C17.xsOf m n) :
    ‖Work.C17I.sw Work.C17.p0C‖ < Work.C17.xsOf m n := by
  have hle : ‖Work.C17I.sw Work.C17.p0C‖ ≤ (1 : ℝ) / 2 := Work.C17.norm_p0C_div_le
  have hhalf : (1 : ℝ) / 2 < 1 - 1 / 100000 := by norm_num
  linarith

end Work.C17I
