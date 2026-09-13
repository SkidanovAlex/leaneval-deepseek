import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.plLE_mul_mul_iff

namespace Commons.LinearAlgebra.Matrix

/-- `plLE` is invariant under multiplying on the left by an injective matrix and on the right by a
surjective matrix. -/
theorem plLE_mul_mul_iff_of_inj_surj {K : Type*} [Field K] {a b p q : ℕ}
    (M : Matrix (Fin a) (Fin b) K) (S : Matrix (Fin q) (Fin p) K)
    (U U' : Matrix (Fin b) (Fin q) K)
    (hM : Function.Injective M.mulVecLin) (hS : Function.Surjective S.mulVecLin) :
    ((M * U' * S).rank = (M * U * S).rank + (M * U' * S - M * U * S).rank) ↔
      U'.rank = U.rank + (U' - U).rank := by
  exact plLE_mul_mul_iff M S U U' (LinearMap.ker_eq_bot.mpr hM) (LinearMap.range_eq_top.mpr hS)

end Commons.LinearAlgebra.Matrix
