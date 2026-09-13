import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.rank_eq_zero_iff

namespace Commons.LinearAlgebra.Matrix

theorem rank_poset_antisymm {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y : Matrix m n K) (h1 : Y.rank = X.rank + (Y - X).rank)
    (h2 : X.rank = Y.rank + (X - Y).rank) : X = Y := by
  have hr : (Y - X).rank = 0 := by omega
  exact (sub_eq_zero.mp ((rank_eq_zero_iff (Y - X)).mp hr)).symm

end Commons.LinearAlgebra.Matrix
