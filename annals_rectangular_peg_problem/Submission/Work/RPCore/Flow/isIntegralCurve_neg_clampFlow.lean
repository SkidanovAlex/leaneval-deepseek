import Mathlib
import Submission.Work.RPCore.Flow.HamFlow

namespace Work.RPCore.Flow

theorem isIntegralCurve_neg_clampFlow (Hh : Work.RPV.CptPerHam) (y : ℝ × Work.RPV.PS) :
    IsIntegralCurve (fun t : ℝ => Work.RPCore.clampFlow Hh (-t) y)
      (fun _ z => -Work.RPCore.clampedField Hh z) := by
  -- reversing time reverses the field: `IsIntegralCurve.comp_mul` with `a = -1`.
  have h := (Work.RPCore.clampFlow_curve Hh y).comp_mul (-1)
  convert h using 1 <;> ext s <;> simp

end Work.RPCore.Flow
