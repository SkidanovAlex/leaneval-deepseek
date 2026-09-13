import Mathlib.LinearAlgebra.Matrix.Rank

namespace Commons.LinearAlgebra.Matrix

theorem rank_le_of_sub {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y : Matrix m n K) (h : Y.rank = X.rank + (Y - X).rank) : X.rank ≤ Y.rank := by
  rw [h]
  exact Nat.le_add_right _ _

end Commons.LinearAlgebra.Matrix