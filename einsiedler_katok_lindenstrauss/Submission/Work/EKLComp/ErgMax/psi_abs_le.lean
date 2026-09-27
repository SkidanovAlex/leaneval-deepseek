import Mathlib
import Submission.Work.EKLComp.ErgMax.ShiftDefs

namespace Work.EKLComp.ErgMax

open MeasureTheory
open Work.EKLContract

/-- `psi ν f u v` is a (Bochner) integral of the `aPlus u v`-translate of `f` against the
probability measure `ν`, so its absolute value is bounded by the sup-norm `‖f‖` of `f`. -/
theorem psi_abs_le (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure ν]
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) (u v : ℝ) :
    |Work.EKLComp.ErgMax.psi ν f u v| ≤ ‖f‖ := by
  rw [psi_apply, ← Real.norm_eq_abs]
  calc ‖∫ y, f (aPlus u v • y) ∂ν‖
      ≤ ‖f‖ * ν.real Set.univ :=
        norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun x => BoundedContinuousFunction.norm_coe_le_norm f _)
    _ = ‖f‖ := by simp

end Work.EKLComp.ErgMax
