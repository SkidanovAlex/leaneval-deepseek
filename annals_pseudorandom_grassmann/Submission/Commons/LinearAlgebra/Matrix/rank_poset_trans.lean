import Mathlib.LinearAlgebra.Matrix.Rank
import Submission.Commons.LinearAlgebra.Matrix.rank_add_le

namespace Commons.LinearAlgebra.Matrix

theorem rank_poset_trans {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y Z : Matrix m n K) (hXY : Y.rank = X.rank + (Y - X).rank)
    (hYZ : Z.rank = Y.rank + (Z - Y).rank) : Z.rank = X.rank + (Z - X).rank := by
  -- The rank of `Z - X = (Y - X) + (Z - Y)` is at most `rank (Y - X) + rank (Z - Y)`.
  have h1 : (Z - X).rank ≤ (Y - X).rank + (Z - Y).rank := by
    have h : Z - X = (Y - X) + (Z - Y) := by abel
    rw [h]
    exact rank_add_le _ _
  -- The rank of `Z = X + (Z - X)` is at most `rank X + rank (Z - X)`.
  have h2 : Z.rank ≤ X.rank + (Z - X).rank := by
    have h : Z = X + (Z - X) := by abel
    calc Z.rank = (X + (Z - X)).rank := congrArg (fun W : Matrix m n K => W.rank) h
      _ ≤ X.rank + (Z - X).rank := rank_add_le _ _
  -- Additivity of `rank` on the two legs gives `rank Z = rank X + rank (Y - X) + rank (Z - Y)`.
  have hZ : Z.rank = X.rank + (Y - X).rank + (Z - Y).rank := by
    rw [hYZ, hXY]
  -- Combining `h2` with `hZ` yields the reverse inequality.
  have h3 : (Y - X).rank + (Z - Y).rank ≤ (Z - X).rank := by
    have hle := h2
    rw [hZ] at hle
    omega
  have hd : (Z - X).rank = (Y - X).rank + (Z - Y).rank := le_antisymm h1 h3
  rw [hZ, hd]
  omega

end Commons.LinearAlgebra.Matrix
