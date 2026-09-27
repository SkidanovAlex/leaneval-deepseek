import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

namespace Work.EKLComp

open Work.EKLContract

/-- The underlying matrix of the inverse of a transvection: `(u_ij(s))⁻¹ = 1 - s E_ij`. -/
lemma toMat_uij_inv {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    toMat ((uij h s)⁻¹) = 1 + Matrix.single i j (-s) := by
  rw [show (uij h s)⁻¹ = uij h (-s) from Matrix.SpecialLinearGroup.transvection_inv h s]
  exact Matrix.SpecialLinearGroup.transvection_coe h (-s)

theorem uij_step_matrix (X Y : ℝ) (A : Work.EKLContract.SL3) :
    Work.EKLContract.toMat
        ((Work.EKLContract.uij (show (1 : Fin 3) ≠ 0 by decide) X *
          Work.EKLContract.uij (show (2 : Fin 3) ≠ 0 by decide) Y)⁻¹ * A)
      = (1 + Matrix.single (1 : Fin 3) 0 (-X) + Matrix.single (2 : Fin 3) 0 (-Y)) *
          Work.EKLContract.toMat A := by
  have hprod :
      (1 + Matrix.single (2 : Fin 3) (0 : Fin 3) (-Y)) *
          (1 + Matrix.single (1 : Fin 3) (0 : Fin 3) (-X))
        = (1 + Matrix.single (1 : Fin 3) (0 : Fin 3) (-X) +
            Matrix.single (2 : Fin 3) (0 : Fin 3) (-Y) : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]
  rw [Work.EKLContract.toMat_mul, mul_inv_rev, Work.EKLContract.toMat_mul,
      toMat_uij_inv, toMat_uij_inv, hprod]

end Work.EKLComp
