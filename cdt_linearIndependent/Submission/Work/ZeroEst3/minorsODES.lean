import Mathlib
import Submission.Work.ZeroEst.mderiv_defs
import Submission.Work.ZeroEst.mderiv_adjugate_mul

/-!
# `Work.ZeroEst3.minorsODES`

If the columns of a matrix of power series `Ψ` satisfy the first order linear system
`s • Ψ' = N Ψ`, then the determinant of *any* square submatrix of `Ψ` (obtained by selecting
`r` of the columns) satisfies the scalar ODE `s • D' = tr N · D`.

The proof uses Jacobi's formula `(det M)' = tr(adj M · M')` (available as
`Work.ZeroEst.derivative_det_eq_trace`), together with `M · adj M = det M • 1` and the
cyclicity of the trace; no invertibility of `A` (or of `s`) is required.
-/

namespace Work.ZeroEst3

open Matrix

theorem minorsODES {r m : ℕ} (Ψ : Matrix (Fin r) (Fin m) (PowerSeries ℚ))
    (s : PowerSeries ℚ) (N : Matrix (Fin r) (Fin r) (PowerSeries ℚ))
    (hODE : ∀ i j, s * PowerSeries.derivative (R := ℚ) (Ψ i j) = ∑ k, N i k * Ψ k j)
    (S : Fin r → Fin m) :
    s * PowerSeries.derivative (R := ℚ) ((Ψ.submatrix id S).det)
      = (Matrix.trace N) * (Ψ.submatrix id S).det := by
  classical
  -- `A` is the `r × r` submatrix of `Ψ` given by selecting the columns `S 0, …, S (r-1)`.
  set A : Matrix (Fin r) (Fin r) (PowerSeries ℚ) := Ψ.submatrix id S with hAdef
  -- The entrywise derivative of `A` satisfies `s • A' = N * A`.
  have hA : ∀ i t, s * Work.ZeroEst.mderiv A i t = ∑ k, N i k * A k t := by
    intro i t
    simpa [hAdef, Work.ZeroEst.mderiv_apply] using hODE i (S t)
  have hsA : s • Work.ZeroEst.mderiv A = N * A := by
    funext i t
    rw [Matrix.smul_apply, Matrix.mul_apply]
    exact hA i t
  -- Jacobi's formula turns `(det A)'` into `tr(adj A · A')`, and then everything is
  -- the associativity/cyclicity of the trace together with `A · adj A = det A • 1`.
  have hmain : s * PowerSeries.derivative (R := ℚ) A.det = A.det * Matrix.trace N := by
    calc s * PowerSeries.derivative (R := ℚ) A.det
        = s * (A.adjugate * Work.ZeroEst.mderiv A).trace := by
            rw [Work.ZeroEst.derivative_det_eq_trace]
      _ = (s • (A.adjugate * Work.ZeroEst.mderiv A)).trace := by
            rw [Matrix.trace_smul, smul_eq_mul]
      _ = (A.adjugate * (s • Work.ZeroEst.mderiv A)).trace := by
            rw [Matrix.mul_smul]
      _ = (A.adjugate * (N * A)).trace := by rw [hsA]
      _ = ((N * A) * A.adjugate).trace := by rw [Matrix.trace_mul_comm]
      _ = (N * (A * A.adjugate)).trace := by rw [Matrix.mul_assoc]
      _ = (N * (A.det • 1)).trace := by rw [Matrix.mul_adjugate]
      _ = (A.det • N).trace := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = A.det * Matrix.trace N := by rw [Matrix.trace_smul, smul_eq_mul]
  calc s * PowerSeries.derivative (R := ℚ) A.det = A.det * Matrix.trace N := hmain
    _ = Matrix.trace N * A.det := mul_comm _ _

end Work.ZeroEst3
