import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.posDef_dotProduct_le_trace_mul_inv_dot
import Submission.Commons.LinearAlgebra.Matrix.trace_mul_ge_of_quadform_ge
import Submission.Commons.LinearAlgebra.Matrix.inv_quadform_ge_of_quadform_le

open scoped Matrix

set_option linter.unusedVariables false

namespace Commons.LinearAlgebra.Matrix

/-- **Quadratic-form comparison for the inverse (upper bound).**
If `A` is positive definite and its quadratic form dominates `c` times the standard one,
`c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A.mulVec x)` for every `x`, then the quadratic form of `A⁻¹` is dominated
by `1/c` times the standard one.  Equivalently, in the Loewner order, `c • 1 ⪯ A` implies
`A⁻¹ ⪯ (1/c) • 1`.

This is the dual of `inv_quadform_ge_of_quadform_le`; the proof is the mirror image, using the
spectral decomposition `A = U * diagonal lam * Uᵀ` and `c ≤ lam i`. -/
theorem inv_quadform_le_of_quadform_ge {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) (hAc : ∀ x : Fin d → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A.mulVec x)) :
    ∀ x : Fin d → ℝ, x ⬝ᵥ (A⁻¹.mulVec x) ≤ (1 / c) * (x ⬝ᵥ x) := by
  classical
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
  -- Hypothesis in the eigenbasis: `c * ∑ y i^2 ≤ ∑ lam i * y i^2`.
  have hquad : ∀ y : Fin d → ℝ, c * ∑ i, y i ^ 2 ≤ ∑ i, lam i * y i ^ 2 := by
    intro y
    have := hAc (U *ᵥ y)
    rw [hdot y, hnn y] at this
    exact this
  -- Every eigenvalue is at least `c`.
  have hlam_ge : ∀ j, c ≤ lam j := by
    intro j
    have h := hquad (Pi.single j (1 : ℝ))
    have h1 : ∑ i, lam i * ((Pi.single j (1 : ℝ) : Fin d → ℝ) i) ^ 2 = lam j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; rw [Pi.single_eq_of_ne hi]; ring
      · intro hh; exact absurd (Finset.mem_univ j) hh
    have h2 : ∑ i, ((Pi.single j (1 : ℝ) : Fin d → ℝ) i) ^ 2 = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; rw [Pi.single_eq_of_ne hi]; ring
      · intro hh; exact absurd (Finset.mem_univ j) hh
    rw [h1, h2, mul_one] at h
    exact h
  -- `A⁻¹ = U * diagonal (λ⁻¹) * Uᵀ`.
  have hdiag : Matrix.diagonal lam * Matrix.diagonal (fun i => (lam i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => lam i * (lam i)⁻¹) = (fun _ => (1 : ℝ)) from
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
  simpa [one_div] using inv_anti₀ hc (hlam_ge i)

/-- **Trace comparison (upper bound).**
If the quadratic form of a symmetric matrix `C` is bounded above by `c₁ * ‖·‖²`, then
`trace (C * N) ≤ c₁ * trace N` for every positive semidefinite `N`.  This is the dual of
`trace_mul_ge_of_quadform_ge`. -/
theorem trace_mul_le_of_quadform_le {d : ℕ} (C N : Matrix (Fin d) (Fin d) ℝ)
    (hC : C.IsSymm) (hN : N.IsSymm) (hNpsd : N.PosSemidef) {c₁ : ℝ}
    (h1 : ∀ v : Fin d → ℝ, v ⬝ᵥ (C.mulVec v) ≤ c₁ * (v ⬝ᵥ v)) :
    (C * N).trace ≤ c₁ * N.trace := by
  classical
  -- `c₁ • 1 - C` is positive semidefinite.
  have hApsd : (c₁ • (1 : Matrix (Fin d) (Fin d) ℝ) - C).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · exact (Matrix.isHermitian_iff_isSymm).mpr
        (((Matrix.isSymm_one (α := ℝ) (n := Fin d)).smul c₁).sub hC)
    · intro v
      have hv : v ⬝ᵥ (C *ᵥ v) ≤ c₁ * (v ⬝ᵥ v) := h1 v
      have hcalc : star v ⬝ᵥ ((c₁ • (1 : Matrix (Fin d) (Fin d) ℝ) - C) *ᵥ v)
          = c₁ * (v ⬝ᵥ v) - v ⬝ᵥ (C *ᵥ v) := by
        simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
      rw [hcalc]
      linarith
  have hkey : 0 ≤ ((c₁ • (1 : Matrix (Fin d) (Fin d) ℝ) - C) * N).trace :=
    posSemidef_trace_mul_nonneg hApsd hNpsd
  have htrace : ((c₁ • (1 : Matrix (Fin d) (Fin d) ℝ) - C) * N).trace
      = c₁ * N.trace - (C * N).trace := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul]
  rw [htrace] at hkey
  linarith

/-- For positive definite `A` and symmetric `B`, the trace of `A⁻¹ * B * A⁻¹ * B` is bounded
by `trace (B * B) / c ^ 2` whenever the quadratic form of `A` dominates `c` times the standard
one.  This is the exact dual of `trace_sq_le_mul_trace_inv`. -/
theorem trace_inv_mul_inv_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.IsSymm) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x : Fin n → ℝ, c * (∑ i, x i * x i) ≤ ∑ i, x i * (A.mulVec x) i) :
    (A⁻¹ * B * A⁻¹ * B).trace ≤ (B * B).trace / c ^ 2 := by
  classical
  have hAc : ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A.mulVec x) := by
    intro x
    simpa [dotProduct] using hlow x
  have hAsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hPsymm : (A⁻¹).IsSymm := hAsymm.inv
  have hPpsd : (A⁻¹).PosSemidef := hA.inv.posSemidef
  -- `A ⪰ c • 1` gives `A⁻¹ ⪯ (1 / c) • 1` in quadratic-form form.
  have hPle : ∀ x : Fin n → ℝ, x ⬝ᵥ (A⁻¹.mulVec x) ≤ (1 / c) * (x ⬝ᵥ x) :=
    inv_quadform_le_of_quadform_ge A hA hc hAc
  have hN1symm : (B * A⁻¹ * B).IsSymm := by
    show (B * A⁻¹ * B)ᵀ = B * A⁻¹ * B
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hB.eq, hPsymm.eq]
    simp only [Matrix.mul_assoc]
  have hN1psd : (B * A⁻¹ * B).PosSemidef := by
    have := Matrix.PosSemidef.mul_mul_conjTranspose_same hPpsd B
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq] using this
  have hN2symm : (B * B).IsSymm := by
    show (B * B)ᵀ = B * B
    rw [Matrix.transpose_mul, hB.eq]
  have hN2psd : (B * B).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq]
      using Matrix.posSemidef_conjTranspose_mul_self B
  -- Two applications of the upper-bound trace comparison.
  have h1 := trace_mul_le_of_quadform_le (A⁻¹) (B * A⁻¹ * B) hPsymm hN1symm hN1psd hPle
  have h2 := trace_mul_le_of_quadform_le (A⁻¹) (B * B) hPsymm hN2symm hN2psd hPle
  have hcyc : (B * A⁻¹ * B).trace = (A⁻¹ * (B * B)).trace := by
    rw [← Matrix.mul_assoc A⁻¹ B B]
    exact (Matrix.trace_mul_cycle A⁻¹ B B).symm
  have hassoc : A⁻¹ * B * A⁻¹ * B = A⁻¹ * (B * A⁻¹ * B) := by noncomm_ring
  calc (A⁻¹ * B * A⁻¹ * B).trace
      = (A⁻¹ * (B * A⁻¹ * B)).trace := by rw [hassoc]
    _ ≤ (1 / c) * (B * A⁻¹ * B).trace := h1
    _ = (1 / c) * (A⁻¹ * (B * B)).trace := by rw [hcyc]
    _ ≤ (1 / c) * ((1 / c) * (B * B).trace) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (B * B).trace / c ^ 2 := by
          have hcne : c ≠ 0 := ne_of_gt hc
          field_simp

end Commons.LinearAlgebra.Matrix
