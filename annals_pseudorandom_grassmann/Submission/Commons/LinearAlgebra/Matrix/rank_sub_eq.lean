import Mathlib.LinearAlgebra.Matrix.Rank

namespace Commons.LinearAlgebra.Matrix

/-- Negating a matrix does not change its rank. -/
theorem rank_neg {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (A : Matrix m n K) : (-A).rank = A.rank := by
  rw [Matrix.rank, Matrix.rank]
  have h : (-A).mulVecLin = -A.mulVecLin := by
    ext v
    simp
  rw [h, LinearMap.range_neg]

/-- The rank of `X - Y` equals the rank of `Y - X`. -/
theorem rank_sub_eq {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y : Matrix m n K) : (X - Y).rank = (Y - X).rank := by
  rw [show Y - X = -(X - Y) from (neg_sub X Y).symm, rank_neg]

end Commons.LinearAlgebra.Matrix