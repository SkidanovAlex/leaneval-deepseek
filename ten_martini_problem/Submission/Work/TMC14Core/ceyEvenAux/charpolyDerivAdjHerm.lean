import Mathlib

/-!
# Jacobi's formula for Hermitian matrices

The derivative of the characteristic polynomial of a Hermitian matrix `M` at a point `z` is the
trace of the adjugate of `z • 1 - M` (Jacobi's formula specialised to the diagonal perturbation
`M + t • 1`, whose derivatives are the eigenvalues):

  `(M.charpoly).derivative.eval z = (adjugate (z • 1 - M)).trace`.

The proof diagonalises `M = U * diag (λ_i) * Uᵀ` using the spectral theorem for Hermitian matrices,
transports the adjugate through the unitary conjugation, and evaluates the derivative of the
product of linear factors `∏ i, (X - C λ_i)`.
-/

open Matrix
open scoped BigOperators Polynomial

namespace Work.TMC14Core.ceyEvenAux

/-- Product rule evaluated at a point, for a product of linear factors. -/
lemma prodLinearDerivEval {n : ℕ} (lam : Fin n → ℂ) (z : ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (lam i))).derivative.eval z
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - lam j) := by
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_mul, Polynomial.derivative_X_sub_C, Polynomial.eval_one, mul_one,
      Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- Conjugating `z • 1 - D` by a unitary matrix. -/
lemma smulOneSubConj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) :
    U * (z • 1 - D) * star U = z • 1 - U * D * star U := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]

/-- The adjugate commutes with conjugation by a unitary matrix. -/
lemma adjugateConj {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * Y * star U).adjugate = U * Y.adjugate * star U := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hdet : (star U).det * U.det = 1 := by rw [← Matrix.det_mul, h2, Matrix.det_one]
  have hA : (Matrix.adjugate U) = U.det • star U := by
    calc Matrix.adjugate U = Matrix.adjugate U * U * star U := by
          rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = (U.det • (1 : Matrix (Fin n) (Fin n) ℂ)) * star U := by rw [Matrix.adjugate_mul]
      _ = U.det • star U := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hB : (Matrix.adjugate (star U)) = (star U).det • U := by
    calc Matrix.adjugate (star U) = Matrix.adjugate (star U) * star U * U := by
          rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = ((star U).det • (1 : Matrix (Fin n) (Fin n) ℂ)) * U := by rw [Matrix.adjugate_mul]
      _ = (star U).det • U := by rw [Matrix.smul_mul, Matrix.one_mul]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hA, hB]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hdet, one_smul,
    Matrix.mul_assoc]

/-- The trace is invariant under conjugation by a unitary matrix. -/
lemma traceConj {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * Y * star U).trace = Y.trace := by
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.trace_mul_comm (U * Y) (star U), ← Matrix.mul_assoc, h2, Matrix.one_mul]

/-- Jacobi's formula for Hermitian matrices: the derivative of the characteristic
polynomial at `z` is the trace of the adjugate of `z • 1 - M`. -/
theorem charpolyDerivAdjHerm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) (z : ℂ) :
    (M.charpoly).derivative.eval z = (Matrix.adjugate (z • (1 : Matrix (Fin n) (Fin n) ℂ) - M)).trace := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := ↑(hM.eigenvectorUnitary) with hUdef
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) with hDdef
  have hUmem : U ∈ Matrix.unitaryGroup (Fin n) ℂ := (hM.eigenvectorUnitary).2
  have hMUD : M = U * D * star U := by
    rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply, ← hUdef]
    show U * Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) * star U = U * D * star U
    rw [← hDdef]
  have hchar : (M.charpoly).derivative.eval z
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - ((hM.eigenvalues j : ℝ) : ℂ)) := by
    rw [hM.charpoly_eq]
    exact prodLinearDerivEval (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) z
  have hz : z • 1 - M = U * (z • 1 - D) * star U := by
    rw [hMUD, smulOneSubConj U D hUmem z]
  have hadj : Matrix.adjugate (z • 1 - M) = U * Matrix.adjugate (z • 1 - D) * star U := by
    rw [hz, adjugateConj U _ hUmem]
  have htr : (U * Matrix.adjugate (z • 1 - D) * star U).trace
      = (Matrix.adjugate (z • 1 - D)).trace := traceConj U _ hUmem
  have hdiag : z • 1 - D = Matrix.diagonal (fun i => z - ((hM.eigenvalues i : ℝ) : ℂ)) := by
    rw [hDdef]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  have hadjdiag : (Matrix.adjugate (z • 1 - D)).trace
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - ((hM.eigenvalues j : ℝ) : ℂ)) := by
    rw [hdiag, Matrix.adjugate_diagonal, Matrix.trace_diagonal]
  calc (M.charpoly).derivative.eval z
      = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - ((hM.eigenvalues j : ℝ) : ℂ)) := hchar
    _ = (Matrix.adjugate (z • 1 - D)).trace := hadjdiag.symm
    _ = (U * Matrix.adjugate (z • 1 - D) * star U).trace := htr.symm
    _ = (Matrix.adjugate (z • 1 - M)).trace := by rw [hadj]

end Work.TMC14Core.ceyEvenAux
