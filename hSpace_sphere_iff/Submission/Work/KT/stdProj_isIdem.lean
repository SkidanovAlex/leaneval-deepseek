import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FiberUtil

namespace Work.KT

open Matrix

/-- The standard projection `diag(1_m, 0_m)` is idempotent. -/
theorem stdProj_isIdem {R : Type} [Ring R] (m : ℕ) :
    Mat.IsIdem (⟨m + m, stdProj R m⟩ : Mat R) := by
  show stdProj R m * stdProj R m = stdProj R m
  rw [stdProj, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

end Work.KT
