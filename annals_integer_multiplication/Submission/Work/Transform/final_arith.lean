import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

/-- The final error bookkeeping of Theorem 3.1: `3 T log₂T + 2T + 12D + 19 < 8 T log₂T`
(since `log₂ T ≥ D` and `D = 1729`, while `T ≥ 3`). -/
theorem final_arith (T L : ℕ) (hL : HvdH.D ≤ L) (hT : 3 ≤ T) :
    (3 * (T : ℝ) * L + 2 * T + (12 * (HvdH.D : ℝ) + 19)) < 8 * (T : ℝ) * L := by
  have hDr : (HvdH.D : ℝ) = 1729 := by norm_num [HvdH.D]
  have hLr : (HvdH.D : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hTr : (3 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  nlinarith [hDr, hLr, hTr]

end Work.Transform
