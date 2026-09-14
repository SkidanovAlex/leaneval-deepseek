import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

namespace Commons.LinearAlgebra.Matrix

theorem linearIndependent_rat_of_int {n r : ℕ} (w : Fin r → Fin n → ℤ)
    (h : LinearIndependent ℤ w) :
    LinearIndependent ℚ (fun j : Fin r => fun i : Fin n => (w j i : ℚ)) := by
  change LinearIndependent ℚ (fun j : Fin r => algebraMap ℤ ℚ ∘ w j)
  exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := w)).mpr h

end Commons.LinearAlgebra.Matrix
