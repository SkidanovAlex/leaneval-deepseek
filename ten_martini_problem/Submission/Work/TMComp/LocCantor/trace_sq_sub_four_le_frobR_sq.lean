import Mathlib
import Submission.Work.TMComp.LocCantor.frobR_defs

namespace Work.TMComp.LocCantor

/-- For an `SL₂(ℝ)` matrix, `(tr B)² - 4 ≤ ‖B‖_F² - 2`.

Writing `B = [[a,b],[c,d]]` with `ad - bc = 1`, the difference of the two sides is
`2ad - 2 - b² - c² = 2bc - b² - c² = -(b - c)² ≤ 0`. -/
theorem trace_sq_sub_four_le_frobR_sq (B : Matrix (Fin 2) (Fin 2) ℝ) (hdet : B.det = 1) :
    B.trace ^ 2 - 4 ≤ Work.TMComp.LocCantor.frobR B ^ 2 - 2 := by
  have hdet' : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  rw [frobR_sq, Matrix.trace_fin_two]
  nlinarith [sq_nonneg (B 0 1 - B 1 0)]

end Work.TMComp.LocCantor
