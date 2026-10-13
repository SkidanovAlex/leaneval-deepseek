import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Final.FlatCut

/-- `cut n` is monotone in `n`: both factors of
`cut n z = smoothTransition ((n+1) z - 1) * (1 - smoothTransition (z/(n+1) - 2))` increase with
`n` when `z ≥ 0` (`(n+1) z - 1 ≤ (n+2) z - 1` and `z/(n+2) ≤ z/(n+1)`),
while for `z < 0` the first factor already vanishes. -/
theorem cutMono (n : ℕ) (z : ℝ) : Work.FTS.EllipticEst.cut n z ≤ Work.FTS.EllipticEst.cut (n + 1) z := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 : ((n:ℝ)+1) * z - 1 ≤ ((n:ℝ)+1+1) * z - 1 := by nlinarith
    have h2 : z / ((n:ℝ)+1+1) - 2 ≤ z / ((n:ℝ)+1) - 2 := by
      have h2' : (0:ℝ) < (n:ℝ)+1 := by linarith
      have h4 : z / ((n:ℝ)+1+1) ≤ z / ((n:ℝ)+1) :=
        div_le_div_of_nonneg_left hz h2' (by linarith)
      linarith
    have ha : Real.smoothTransition (((n:ℝ)+1) * z - 1)
        ≤ Real.smoothTransition (((n:ℝ)+1+1) * z - 1) := Real.smoothTransition.monotone h1
    have hb : (1 - Real.smoothTransition (z / ((n:ℝ)+1) - 2)) ≤
        (1 - Real.smoothTransition (z / ((n:ℝ)+1+1) - 2)) := by
      have := Real.smoothTransition.monotone h2
      linarith
    have hb0 : (0:ℝ) ≤ 1 - Real.smoothTransition (z / ((n:ℝ)+1) - 2) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have ha0 : (0:ℝ) ≤ Real.smoothTransition (((n:ℝ)+1) * z - 1) :=
      Real.smoothTransition.nonneg _
    simp only [Work.FTS.EllipticEst.cut]
    push_cast
    exact mul_le_mul ha hb hb0 (le_trans ha0 ha)
  · have h1 : ((n:ℝ)+1) * z - 1 < 0 := by
      have : (0:ℝ) < (n:ℝ)+1 := by positivity
      nlinarith
    have hzero : Real.smoothTransition (((n:ℝ)+1) * z - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos h1.le
    have hnc : Work.FTS.EllipticEst.cut n z = 0 := by
      simp only [Work.FTS.EllipticEst.cut]
      rw [hzero, zero_mul]
    rw [hnc]
    exact Work.FTS.EllipticEst.cut_nonneg _ _

end Work.FTS.EllipticEst.Final.FlatCut
