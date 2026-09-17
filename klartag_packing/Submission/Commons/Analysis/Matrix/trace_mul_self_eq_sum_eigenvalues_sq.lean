import Mathlib.Analysis.Matrix.Spectrum

namespace Commons.Analysis.Matrix

theorem trace_mul_self_eq_sum_eigenvalues_sq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (M * M).trace = ∑ i, (hM.eigenvalues i)^2 := by
  set U : Matrix n n ℝ := ↑hM.eigenvectorUnitary with hU
  set D : Matrix n n ℝ := _root_.Matrix.diagonal (fun i => hM.eigenvalues i) with hD
  -- Spectral decomposition `M = U * D * Uᴴ`.
  have hdecomp : M = U * D * star U := by
    rw [hU, hD]
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    congr 2
  have hUU : star U * U = 1 := by rw [hU]; exact Unitary.coe_star_mul_self _
  -- `M * M` is the conjugation of the squared diagonal matrix.
  have hsq : M * M = U * (D * D) * star U := by
    rw [hdecomp]
    simp only [mul_assoc]
    rw [← mul_assoc (star U) U (D * star U), hUU, one_mul]
  rw [hsq, _root_.Matrix.trace_mul_comm (U * (D * D)) (star U)]
  rw [← mul_assoc, hUU, one_mul]
  rw [hD, _root_.Matrix.diagonal_mul_diagonal]
  simp [_root_.Matrix.trace_diagonal, pow_two]

end Commons.Analysis.Matrix