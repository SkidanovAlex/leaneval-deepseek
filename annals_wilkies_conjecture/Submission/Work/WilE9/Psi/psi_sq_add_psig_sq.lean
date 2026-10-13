import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- `(psi x, psig x)` lies on the unit circle. -/
theorem psi_sq_add_psig_sq (x : ℝ) :
    WilkiesDesign.E.psi x ^ 2 + Work.WilE9.psig x ^ 2 = 1 := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  unfold WilkiesDesign.E.psi Work.WilE9.psig
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt hpos)]

end Work.WilE9.Psi
