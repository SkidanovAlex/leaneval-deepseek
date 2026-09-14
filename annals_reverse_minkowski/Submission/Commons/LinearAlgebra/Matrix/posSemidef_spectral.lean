import Mathlib.Analysis.Matrix.PosDef

namespace Commons.LinearAlgebra.Matrix

theorem posSemidef_spectral {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    ∃ (V : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      V.transpose * V = 1 ∧ (∀ i, 0 ≤ d i) ∧ M = V.transpose * Matrix.diagonal d * V := by
  classical
  refine ⟨(hM.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose,
    hM.isHermitian.eigenvalues, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (hM.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  · exact fun i => hM.eigenvalues_nonneg i
  · rw [Matrix.transpose_transpose]
    refine (hM.isHermitian.spectral_theorem).trans ?_
    rw [Unitary.conjStarAlgAut_apply]
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

end Commons.LinearAlgebra.Matrix