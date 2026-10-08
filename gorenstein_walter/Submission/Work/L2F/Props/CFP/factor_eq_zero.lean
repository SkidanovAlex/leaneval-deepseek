import Mathlib

namespace Work.L2F.Props.CFP

/-- Cayley–Hamilton factorisation for a `2 × 2` matrix.

If `M : Matrix (Fin 2) (Fin 2) F` has determinant `1` and `v ≠ 0` is an eigenvector of `M` with
eigenvalue `c`, then `(M - c • 1) * (M - c⁻¹ • 1) = 0`.

Indeed `c` is a root of the characteristic polynomial `t² - tr(M)·t + det(M)`, so the other root
satisfies `c · e = det(M) = 1`, i.e. `e = c⁻¹` and `tr(M) = c + c⁻¹`. Cayley–Hamilton then reads
`M² - (c + c⁻¹)·M + 1 = 0`, which is `(M - c·1)(M - c⁻¹·1) = 0`, using `c · c⁻¹ = 1`. -/
private theorem factor_eq_zero_of_det_one (F : Type*) [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (v : Fin 2 → F) (hv : v ≠ 0) (c : F) (hdet : M.det = 1)
    (hXv : Matrix.mulVec M v = c • v) :
    (M - c • 1) * (M - c⁻¹ • 1) = 0 := by
  -- `v` lies in the kernel of `M - c • 1`.
  have hker : Matrix.mulVec (M - c • 1) v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hXv, sub_self]
  -- A matrix with a nontrivial kernel has determinant `0`.
  have hdet0 : (M - c • 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hker⟩
  -- Hence `det (M - c • 1) = det M - c · tr M + c² = 0`.
  have hdetc : (M - c • 1).det = M.det - c * M.trace + c^2 := by
    rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    simp [Matrix.sub_apply, Matrix.smul_apply]
    ring
  have hct : c * M.trace = 1 + c^2 := by
    rw [hdetc, hdet] at hdet0
    linear_combination -hdet0
  -- `c ≠ 0`, so the eigenvalue and its inverse multiply to `1`.
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at hct
    simp at hct
  have htrace : M.trace = c + c⁻¹ := by
    have h2 : c * M.trace = c * (c + c⁻¹) := by
      rw [hct, mul_add, mul_inv_cancel₀ hc]
      ring
    exact mul_left_cancel₀ hc h2
  -- Cayley–Hamilton in dimension `2`.
  have hCH : M * M - M.trace • M + M.det • 1 = 0 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply] <;>
      ring
  -- Expand the product with the two linear factors.
  have hgen : (M - c • 1) * (M - c⁻¹ • 1) =
      M * M - (c + c⁻¹) • M + (c * c⁻¹) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply] <;>
      ring
  rw [hgen, mul_inv_cancel₀ hc, one_smul]
  rw [htrace, hdet, one_smul] at hCH
  exact hCH

theorem factor_eq_zero (F : Type*) [Field F] (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) (hv : v ≠ 0) (c : F)
    (hXv : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = c • v) :
    ((X : Matrix (Fin 2) (Fin 2) F) - c • 1) *
      ((X : Matrix (Fin 2) (Fin 2) F) - c⁻¹ • 1) = 0 :=
  factor_eq_zero_of_det_one F (X : Matrix (Fin 2) (Fin 2) F) v hv c
    (Matrix.SpecialLinearGroup.det_coe X) hXv

end Work.L2F.Props.CFP
