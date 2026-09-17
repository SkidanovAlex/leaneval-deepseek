import Mathlib.LinearAlgebra.Matrix.Cartan

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- The `E₈` Cartan matrix is symmetric, has diagonal entries `2`, and every off-diagonal
entry is either `0` or `-1`. -/
theorem E8_diag_offdiag_symm :
    (∀ i j : Fin 8, CartanMatrix.E₈ i j = CartanMatrix.E₈ j i) ∧
    (∀ i : Fin 8, CartanMatrix.E₈ i i = 2) ∧
    (∀ i j : Fin 8, i ≠ j → CartanMatrix.E₈ i j = 0 ∨ CartanMatrix.E₈ i j = -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | decide

end Commons.LinearAlgebra.Matrix.Cartan