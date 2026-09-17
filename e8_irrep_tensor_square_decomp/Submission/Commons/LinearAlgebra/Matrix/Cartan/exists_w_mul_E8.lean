import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- There is a left-inverse row vector for the `E₈` Cartan matrix over `ℂ`: some `w` with
`∑ j, w j * (E₈) j i = 1` for every column `i`.  Equivalently `w ᵥ* E₈ = (1, …, 1)`.

This holds because the `E₈` Cartan matrix is invertible (its determinant is `1`), so the
row-vector map `w ↦ w ᵥ* E₈` is surjective. -/
theorem exists_w_mul_E8 :
    ∃ w : Fin 8 → ℂ, ∀ i : Fin 8, ∑ j, w j * ((CartanMatrix.E₈) j i : ℂ) = 1 := by
  classical
  set M : Matrix (Fin 8) (Fin 8) ℂ := CartanMatrix.E₈.map (fun x : ℤ => (x : ℂ)) with hM
  have hdet : M.det = 1 := by
    rw [hM, ← Int.cast_det, (show CartanMatrix.E₈.det = 1 from CartanMatrix.E₈_det)]
    norm_num
  have hunit : IsUnit M.det := by rw [hdet]; exact isUnit_one
  obtain ⟨w, hw⟩ :=
    (Matrix.vecMul_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det M).2 hunit))
      (fun _ : Fin 8 => (1 : ℂ))
  refine ⟨w, fun i => ?_⟩
  have h := congrFun hw i
  simpa [hM, Matrix.vecMul_apply_eq_sum] using h

end Commons.LinearAlgebra.Matrix.Cartan