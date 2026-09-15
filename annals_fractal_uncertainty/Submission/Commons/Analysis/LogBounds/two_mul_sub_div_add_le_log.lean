import Submission.Commons.Analysis.Real.two_mul_sub_div_add_le_log

namespace Commons.Analysis.LogBounds

/-- The arithmetic–harmonic–logarithmic lower bound `2(y-1)/(y+1) ≤ log y` for
`y ≥ 1`. Re-exports the proven commons lemma
`Commons.Analysis.Real.two_mul_sub_div_add_le_log`. -/
theorem two_mul_sub_div_add_le_log (y : ℝ) (hy : 1 ≤ y) :
    2 * (y - 1) / (y + 1) ≤ Real.log y :=
  Commons.Analysis.Real.two_mul_sub_div_add_le_log (x := y) hy

end Commons.Analysis.LogBounds
