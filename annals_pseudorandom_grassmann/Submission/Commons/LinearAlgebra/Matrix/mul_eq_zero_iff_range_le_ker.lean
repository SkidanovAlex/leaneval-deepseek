import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Commons.LinearAlgebra.Matrix

theorem mul_eq_zero_iff_range_le_ker {K : Type*} [Field K] {m n p : ℕ}
    (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin p) K) :
    M * N = 0 ↔ LinearMap.range (Matrix.mulVecLin N) ≤ LinearMap.ker (Matrix.mulVecLin M) := by
  constructor
  · intro h
    rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_zero]
  · intro h
    have hcomp : (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) = 0 :=
      LinearMap.range_le_ker_iff.mp h
    have hlin : Matrix.mulVecLin (M * N) =
        Matrix.mulVecLin (0 : Matrix (Fin m) (Fin p) K) := by
      rw [Matrix.mulVecLin_mul, hcomp, Matrix.mulVecLin_zero]
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using hlin)

end Commons.LinearAlgebra.Matrix