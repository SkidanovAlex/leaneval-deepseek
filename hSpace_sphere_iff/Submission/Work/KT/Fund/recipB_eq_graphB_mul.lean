import Mathlib
import Submission.Work.KT.Fund.Clutch

namespace Work.KT.Fund

open Matrix

/-- `graphB R N = [[1],[N]]` and `recipB R M = [[M],[1]]`.  Since `N * M = 1`, the top block of
`graphB R N * M` is `1 * M = M` and its bottom block is `N * M = 1`, so it agrees with
`recipB R M`. -/
theorem recipB_eq_graphB_mul {n : ℕ} (R : Type) [Ring R]
    (M N : Matrix (Fin n) (Fin n) R) (h : N * M = 1) :
    Work.KT.Fund.recipB R M = Work.KT.Fund.graphB R N * M := by
  ext i j
  cases i with
  | inl a =>
    simp [Work.KT.Fund.graphB, Work.KT.Fund.recipB, Matrix.mul_apply]
  | inr a =>
    simp only [Work.KT.Fund.graphB, Work.KT.Fund.recipB, Matrix.mul_apply]
    rw [← Matrix.mul_apply, h, Matrix.one_apply]

end Work.KT.Fund
