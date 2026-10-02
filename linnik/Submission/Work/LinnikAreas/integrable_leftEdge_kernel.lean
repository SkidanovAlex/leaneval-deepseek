import Mathlib
import Submission.Commons.Analysis.Integral.integrable_log_lorentz

namespace Work.LinnikAreas

/-- The left-edge tent kernel `t ↦ (1 + log (|t| + 2)) / (9/4 + t²)` is Lebesgue-integrable
on `ℝ`: the logarithmic growth is beaten by the quadratic decay.  This is the specialisation
`a = 3/2`, `b = 0` of the general Lorentzian-dominance lemma
`Commons.Analysis.Integral.integrable_log_lorentz`. -/
theorem integrable_leftEdge_kernel :
    MeasureTheory.Integrable (fun t : ℝ => (1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2)) := by
  have h := Commons.Analysis.Integral.integrable_log_lorentz (3 / 2) 0 (by norm_num)
  convert h using 1
  ext t
  simp only [sub_zero]
  rw [show (9 : ℝ) / 4 = (3 / 2) ^ 2 by norm_num]
  ring_nf

end Work.LinnikAreas
