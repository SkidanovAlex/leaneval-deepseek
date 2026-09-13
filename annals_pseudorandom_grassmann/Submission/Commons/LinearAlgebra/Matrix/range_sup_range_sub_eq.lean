import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.PicardGroup

namespace Commons.LinearAlgebra.Matrix

theorem range_sup_range_sub_eq {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (X Y : Matrix m n K) (h : Y.rank = X.rank + (Y - X).rank) :
    LinearMap.range Y.mulVecLin = LinearMap.range X.mulVecLin ⊔ LinearMap.range (Y - X).mulVecLin
    := by
  have hYX : X + (Y - X) = Y := by abel
  have hlin : Y.mulVecLin = X.mulVecLin + (Y - X).mulVecLin := by
    conv_lhs => rw [← hYX]
    exact Matrix.mulVecLin_add X (Y - X)
  have hsub : LinearMap.range Y.mulVecLin ≤
      LinearMap.range X.mulVecLin ⊔ LinearMap.range (Y - X).mulVecLin := by
    rw [hlin]
    exact LinearMap.range_add_le _ _
  refine Submodule.eq_of_le_of_finrank_le hsub ?_
  calc Module.finrank K ↥(LinearMap.range X.mulVecLin ⊔ LinearMap.range (Y - X).mulVecLin)
      ≤ Module.finrank K ↥(LinearMap.range X.mulVecLin) +
          Module.finrank K ↥(LinearMap.range (Y - X).mulVecLin) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = X.rank + (Y - X).rank := rfl
    _ = Y.rank := h.symm
    _ = Module.finrank K ↥(LinearMap.range Y.mulVecLin) := rfl

end Commons.LinearAlgebra.Matrix