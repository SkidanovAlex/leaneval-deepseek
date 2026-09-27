import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- The entries of the shear `u_ij(s) = 1 + s E_ij`:
it is `1` on the diagonal, `s` at position `(i,j)`, and `0` elsewhere. -/
theorem uij_coe_apply {i j : Fin 3} (h : i ≠ j) (s : ℝ) (k l : Fin 3) :
    (uij h s : Matrix (Fin 3) (Fin 3) ℝ) k l =
      if k = l then 1 else if k = i ∧ l = j then s else 0 := by
  rw [uij, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs with h1 h2 h3
  · exfalso; simp_all
  · ring
  · ring
  · exfalso; simp_all
  · exfalso; simp_all
  · ring

theorem uij_api (s t : ℝ) {i j : Fin 3} (h : i ≠ j) :
    (uij h 0 = 1) ∧ (uij h s * uij h t = uij h (s + t)) ∧ ((uij h s)⁻¹ = uij h (-s)) ∧
    (∀ k l : Fin 3, (uij h s : Matrix (Fin 3) (Fin 3) ℝ) k l
      = if k = l then 1 else if k = i ∧ l = j then s else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  · simp [uij, Matrix.SpecialLinearGroup.transvection_add]
  · simp [uij, Matrix.SpecialLinearGroup.transvection_inv]
  · exact uij_coe_apply h s

end Work.EKLC8Core
