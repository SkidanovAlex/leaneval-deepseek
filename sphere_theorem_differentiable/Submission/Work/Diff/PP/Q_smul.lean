import Mathlib
import Submission.Work.Diff.PP.deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.PP

open Submission.Diff.Alg

/-- `Q` is homogeneous of degree two: `Q (c • R) = c² • Q R`. (Each term of the defining sum is a
product of two entries of `R`.) -/
theorem Q_smul (n : ℕ) (c : ℝ) (R : Curv4 n) : Q (c • R) = c ^ 2 • Q R := by
  ext i j k l
  simp only [Q, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

end Work.Diff.PP
