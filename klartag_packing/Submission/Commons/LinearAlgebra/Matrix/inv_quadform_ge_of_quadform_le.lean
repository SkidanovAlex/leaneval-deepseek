import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.posDef_dotProduct_le_trace_mul_inv_dot

open scoped Matrix

namespace Commons.LinearAlgebra.Matrix

/-- **Quadratic-form comparison for the inverse.**
If `A` is positive definite and its quadratic form is dominated by `c` times the standard
one, `x ⬝ᵥ (A.mulVec x) ≤ c * (x ⬝ᵥ x)` for every `x`, then the quadratic form of `A⁻¹`
dominates `1/c` times the standard one.  Equivalently, in the Loewner order,
`A ⪯ c • 1` implies `(1/c) • 1 ⪯ A⁻¹`. -/
theorem inv_quadform_ge_of_quadform_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) (hAc : ∀ x : Fin d → ℝ, x ⬝ᵥ (A.mulVec x) ≤ c * (x ⬝ᵥ x)) :
    ∀ x : Fin d → ℝ, (1 / c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A⁻¹.mulVec x) := by
  classical
  have _ : 0 < c := hc
  -- Spectral decomposition `A = U * diagonal lam * Uᵀ` with `U` orthogonal and `lam > 0`.
  let U : Matrix (Fin d) (Fin d) ℝ := hA.isHermitian.eigenvectorUnitary
  let lam : Fin d → ℝ := hA.isHermitian.eigenvalues
  have hU1 : Uᵀ * U = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ), ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hU2 : U * Uᵀ = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ), ← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal lam * Uᵀ := by
    have h := hA.isHermitian.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simpa [U, lam] using h
  have hlampos : ∀ i, 0 < lam i := fun i => hA.eigenvalues_pos i
  have hUTU_mulvec : ∀ y : Fin d → ℝ, Uᵀ *ᵥ (U *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
  -- Quadratic forms expressed in the eigenbasis.
  have hdot : ∀ y : Fin d → ℝ, (U *ᵥ y) ⬝ᵥ (A.mulVec (U *ᵥ y)) = ∑ i, lam i * y i ^ 2 := by
    intro y
    have h := dotProduct_mulVec_eq_sum_eigenvalues_sq A hA.isHermitian (U *ᵥ y)
    rw [hUTU_mulvec y] at h
    simpa [U, lam] using h
  have hnn : ∀ y : Fin d → ℝ, (U *ᵥ y) ⬝ᵥ (U *ᵥ y) = ∑ i, y i ^ 2 := by
    intro y
    have h := dotProduct_self_eq_sum_sq_mulVec_transpose U hU2 (U *ᵥ y)
    rw [hUTU_mulvec y] at h
    exact h
  -- Since `U` is invertible, the hypothesis `hAc` becomes `∑ lam i * y i ^ 2 ≤ c * ∑ y i ^ 2`.
  have hquad : ∀ y : Fin d → ℝ, ∑ i, lam i * y i ^ 2 ≤ c * ∑ i, y i ^ 2 := by
    intro y
    have := hAc (U *ᵥ y)
    rw [hdot y, hnn y] at this
    exact this
  -- Every eigenvalue is at most `c`.
  have hlam_le : ∀ j, lam j ≤ c := by
    intro j
    have h := hquad (Pi.single j (1:ℝ))
    have h1 : ∑ i, lam i * ((Pi.single j (1:ℝ) : Fin d → ℝ) i)^2 = lam j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; rw [Pi.single_eq_of_ne hi]; ring
      · intro hh; exact absurd (Finset.mem_univ j) hh
    have h2 : ∑ i, ((Pi.single j (1:ℝ) : Fin d → ℝ) i)^2 = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; rw [Pi.single_eq_of_ne hi]; ring
      · intro hh; exact absurd (Finset.mem_univ j) hh
    rw [h1, h2, mul_one] at h
    exact h
  -- `A⁻¹ = U * diagonal (λ⁻¹) * Uᵀ`.
  have hdiag : Matrix.diagonal lam * Matrix.diagonal (fun i => (lam i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => lam i * (lam i)⁻¹) = (fun _ => (1:ℝ)) from
      funext (fun i => mul_inv_cancel₀ (ne_of_gt (hlampos i)))]
    rw [Matrix.diagonal_one]
  have hAinv : A⁻¹ = U * Matrix.diagonal (fun i => (lam i)⁻¹) * Uᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hspec]
    calc (U * Matrix.diagonal lam * Uᵀ) * (U * Matrix.diagonal (fun i => (lam i)⁻¹) * Uᵀ)
        = U * Matrix.diagonal lam * (Uᵀ * U) * Matrix.diagonal (fun i => (lam i)⁻¹) * Uᵀ := by
          noncomm_ring
      _ = U * Matrix.diagonal lam * 1 * Matrix.diagonal (fun i => (lam i)⁻¹) * Uᵀ := by rw [hU1]
      _ = U * (Matrix.diagonal lam * Matrix.diagonal (fun i => (lam i)⁻¹)) * Uᵀ := by noncomm_ring
      _ = U * 1 * Uᵀ := by rw [hdiag]
      _ = 1 := by rw [Matrix.mul_one, hU2]
  -- Quadratic forms in the eigenbasis.
  have hx1 : ∀ x : Fin d → ℝ, x ⬝ᵥ x = ∑ i, (Uᵀ *ᵥ x) i ^ 2 := by
    intro x
    exact dotProduct_self_eq_sum_sq_mulVec_transpose U hU2 x
  have hx2 : ∀ x : Fin d → ℝ,
      x ⬝ᵥ (A⁻¹.mulVec x) = ∑ i, (lam i)⁻¹ * (Uᵀ *ᵥ x) i ^ 2 := by
    intro x
    rw [hAinv]
    rw [show (U * Matrix.diagonal (fun i => (lam i)⁻¹) * Uᵀ) *ᵥ x
        = U *ᵥ (Matrix.diagonal (fun i => (lam i)⁻¹) *ᵥ (Uᵀ *ᵥ x)) from by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
    rw [Matrix.dotProduct_mulVec, show Uᵀ *ᵥ x = x ᵥ* U from Matrix.mulVec_transpose U x]
    simp only [Matrix.mulVec_diagonal, dotProduct, sq]
    apply Finset.sum_congr rfl
    intro i _
    ring
  intro x
  rw [hx1 x, hx2 x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := inv_anti₀ (hlampos i) (hlam_le i)
  simpa [one_div] using h

end Commons.LinearAlgebra.Matrix

