import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Matrix

/-- The rank of a sum of matrices is at most the sum of their ranks. -/
theorem rank_add_le {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↑(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)
    _ ≤ Module.finrank K ↑(LinearMap.range A.mulVecLin)
          + Module.finrank K ↑(LinearMap.range B.mulVecLin) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _

end Commons.LinearAlgebra.Matrix