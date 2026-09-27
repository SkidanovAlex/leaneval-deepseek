import Mathlib
import Submission.Work.EKLContract.Diag

namespace Work.EKLProd

/-- `aDiag` sends repeated addition of `t` to powers of `aDiag t`. -/
theorem aDiag_nsmul (t : Fin 3 → ℝ) (n : ℕ) :
    Work.EKLContract.aDiag (n • t) = Work.EKLContract.aDiag t ^ n := by
  induction n with
  | zero => rw [zero_nsmul, Work.EKLContract.aDiag_zero, pow_zero]
  | succ n ih =>
    rw [succ_nsmul, ← Work.EKLContract.aDiag_add, ih, pow_succ]

end Work.EKLProd
