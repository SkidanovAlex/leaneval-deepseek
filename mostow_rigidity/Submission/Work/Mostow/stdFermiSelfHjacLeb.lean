import Mathlib
import Submission.Work.Mostow.stdFermiDefs
import Submission.Work.Mostow.VolDefs

namespace Work.Mostow

/-- The hyperbolic Jacobian weight of the standard Fermi self-chart of `E 2`, read off from the
determinant of its derivative and the value of `tpart` at its image. -/
theorem stdFermiSelfHjacLeb (x : Submission.Mostow.E 2)
    (hdet : (fderiv ℝ Work.Mostow.FermiTwo.fermiSelf x).det =
      Real.cosh (x 1) ^ 2 * Real.cosh (x 0))
    (htp : Submission.Mostow.tpart (Work.Mostow.FermiTwo.fermiSelf x) =
      Real.cosh (x 0) * Real.cosh (x 1)) :
    Work.Mostow.hjacLeb Work.Mostow.FermiTwo.fermiSelf x = ENNReal.ofReal (Real.cosh (x 1)) := by
  simp only [Work.Mostow.hjacLeb, Work.Mostow.hdens]
  rw [hdet, htp]
  rw [abs_of_nonneg (by positivity)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end Work.Mostow
