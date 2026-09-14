import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.LinearAlgebra.Matrix

theorem det_map_int_real {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) :
    (A.map (fun z : ℤ => (z : ℝ))).det = ((A.det : ℤ) : ℝ) := by
  exact (Int.cast_det A).symm

end Commons.LinearAlgebra.Matrix