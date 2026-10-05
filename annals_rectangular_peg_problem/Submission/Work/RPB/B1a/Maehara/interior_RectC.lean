import Mathlib
import Submission.Work.RPB.B1a.Maehara.Defs

open Set Complex

namespace Work.RPB.B1a.Maehara

/-- `RectC` is the `reProdIm`-rectangle of the closed intervals `[-1,1]` (real part) and
`[-2,2]` (imaginary part). -/
theorem RectC_eq_reProdIm :
    RectC = Set.Icc (-1 : ℝ) 1 ×ℂ Set.Icc (-2 : ℝ) 2 := by
  ext z; simp [RectC, Complex.mem_reProdIm, and_assoc]

theorem interior_RectC :
    interior RectC = {z : ℂ | -1 < z.re ∧ z.re < 1 ∧ -2 < z.im ∧ z.im < 2} := by
  rw [RectC_eq_reProdIm, interior_reProdIm, interior_Icc, interior_Icc]
  ext z; simp [Complex.mem_reProdIm, and_assoc]

end Work.RPB.B1a.Maehara
