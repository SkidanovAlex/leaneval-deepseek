import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPV

/-- The parallelogram identity for `ℂ`, in the exact shape needed below:
`(‖z‖² + ‖w‖²)/2 = ‖(z+w)/√2‖²/2 + ‖z-w‖²/4`. -/
private lemma norm_sq_identity (z w : ℂ) :
    (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 - 1
      = ‖(z + w) / (Real.sqrt 2 : ℂ)‖ ^ 2 / 2 - (-(‖z - w‖ ^ 2) / 4) - 1 := by
  have h2 : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdiv : Complex.normSq ((z + w) / (Real.sqrt 2 : ℂ))
      = (Complex.normSq z + Complex.normSq w + 2 * (z * (starRingEnd ℂ) w).re) / 2 := by
    rw [Complex.normSq_div, Complex.normSq_add, h2]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, hdiv,
    Complex.normSq_sub]
  ring

theorem chordPS_levelPt (z w : ℂ) (a : ℝ) :
    Work.RPV.chordPS z w a =
      Work.RPV.levelPt ((z + w) / (Real.sqrt 2 : ℂ)) (-(‖z - w‖ ^ 2) / 4) a := by
  have key := norm_sq_identity z w
  simp only [Work.RPV.chordPS, Work.RPV.levelPt]
  rw [key]

end Work.RPV
