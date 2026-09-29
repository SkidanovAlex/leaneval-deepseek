import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one

namespace Work.TMC7Core.Cocycle

/-- Every iterate of the transfer cocycle has determinant one, hence Frobenius norm at
least `√2 > 1`; the logarithm is therefore nonnegative. -/
theorem log_frob_iterC_nonneg (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) : 0 ≤ Real.log (frob (iterC α lam E n x)) := by
  have h1 : (1 : ℝ) ≤ frob (iterC α lam E n x) :=
    le_trans (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2])
      (frob_sqrt_two_le_of_det_one (det_iterC α lam E n x))
  calc (0 : ℝ) = Real.log 1 := Real.log_one.symm
    _ ≤ Real.log (frob (iterC α lam E n x)) := Real.log_le_log one_pos h1

end Work.TMC7Core.Cocycle
