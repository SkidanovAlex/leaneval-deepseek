import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped Matrix

namespace Commons.LinearAlgebra.Matrix.Cartan

theorem reflect_dotProduct_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hsymm : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 2) (hdet : A.det ≠ 0)
    (i : Fin n) (v w : Fin n → ℚ) :
    (fun j => v j - v i * A i j) ⬝ᵥ ((A⁻¹).mulVec (fun j => w j - w i * A i j))
      = v ⬝ᵥ ((A⁻¹).mulVec w) := by
  classical
  have hIsUnit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hIsUnit
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hIsUnit
  -- the reflection vectors are `v - v_i * (row i)` and `w - w_i * (row i)`
  have hu : (fun j => v j - v i * A i j) = v - (v i) • (A.row i) := by
    funext j; simp
  have hw' : (fun j => w j - w i * A i j) = w - (w i) • (A.row i) := by
    funext j; simp
  -- `row i` of `A` is `A *ᵥ eᵢ` (using symmetry)
  have hrow : A.row i = A.mulVec (Pi.single i 1) := by
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.row_apply, Matrix.col_apply]
    exact hsymm i j
  -- hence `A⁻¹ *ᵥ row i = eᵢ`
  have hBrow : A⁻¹ *ᵥ (A.row i) = Pi.single i 1 := by
    rw [hrow, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  -- and `row i ⬝ᵥ A⁻¹ *ᵥ w = w_i`
  have hABw : A.row i ⬝ᵥ (A⁻¹ *ᵥ w) = w i := by
    have h1 : A.row i = Matrix.vecMul (Pi.single i 1) A := by
      rw [Matrix.single_one_vecMul]
    rw [h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    exact single_one_dotProduct i w
  rw [hu, hw']
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hBrow]
  simp only [sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_smul,
    hABw, dotProduct_single_one, Pi.sub_apply, Pi.smul_apply,
    Matrix.row_apply, hdiag, smul_eq_mul]
  ring

end Commons.LinearAlgebra.Matrix.Cartan