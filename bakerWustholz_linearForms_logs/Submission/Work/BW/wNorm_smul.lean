import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `wNorm A c` is absolutely homogeneous: scaling the argument by `t` scales the norm by `|t|`.

This holds even for the degenerate cases `t = 0` (both sides vanish) and without any hypothesis
on `c` or `A`: the weighted `ℓ¹` norm of a linear image inherits absolute homogeneity directly
from `|t * y| = |t| * |y|`. -/
theorem wNorm_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) : Work.BW.wNorm A c (t • x) = |t| * Work.BW.wNorm A c x := by
  unfold Work.BW.wNorm
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end Work.BW
