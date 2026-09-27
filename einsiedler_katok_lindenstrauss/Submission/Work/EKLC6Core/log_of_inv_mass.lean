import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLC6Core.Basic

namespace Work.EKLC6Core

/-- `growthFun U ν t x = -log (ν x (conjBox U t)).toReal`; if the contracted box has mass
`c⁻¹` then the growth is `log c`. -/
theorem log_of_inv_mass {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    (t : Fin 3 → ℝ) (x : Work.EKLContract.X3) {c : ℝ} (hc : 0 < c)
    (h : (ν x (Work.EKLC6Core.conjBox U t)).toReal = c⁻¹) :
    Work.EKLC6Core.growthFun U ν t x = Real.log c := by
  rw [Work.EKLC6Core.growthFun, h, Real.log_inv]
  ring

end Work.EKLC6Core
