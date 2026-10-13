import Mathlib

namespace Work.WilE7.DimAPI

theorem finrank_range_mulVecLin_submatrix_natAdd {N j : ℕ} (A : Matrix (Fin j) (Fin (0 + N)) ℝ) :
    Module.finrank ℝ (LinearMap.range (A.submatrix id (Fin.natAdd 0)).mulVecLin)
      = Module.finrank ℝ (LinearMap.range A.mulVecLin) := by
  -- `Matrix.rank R` is *defined* as the `finrank` of the range of `mulVecLin`,
  -- so the goal is an equality of matrix ranks.
  show (A.submatrix id (Fin.natAdd 0)).rank = A.rank
  -- `Fin.natAdd 0 : Fin N → Fin (0 + N)` is the bijection underlying `finCongr`.
  -- Reindexing columns along a bijection preserves the rank.
  rw [show A.submatrix id (Fin.natAdd 0)
        = A.submatrix (⇑(Equiv.refl (Fin j))) (⇑(finCongr (Nat.zero_add N).symm)) from ?_]
  · exact Matrix.rank_submatrix A _ _
  · ext i k
    simp [Matrix.submatrix, finCongr_apply, Fin.natAdd_zero]

end Work.WilE7.DimAPI
