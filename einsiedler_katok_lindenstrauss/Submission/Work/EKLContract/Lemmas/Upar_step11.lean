import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

namespace Work.EKLContract.Lemmas

open Matrix

/-- The underlying matrix of a root-group element `u_ij(s)` is `1 + s·E_ij`. -/
private theorem toMat_uij {i j : Fin 3} (h : i ≠ j) (s : ℝ) :
    Work.EKLContract.toMat (Work.EKLContract.uij h s) = 1 + Matrix.single i j s := by
  rw [Work.EKLContract.uij]
  exact Matrix.SpecialLinearGroup.transvection_coe h s

/-- `u_02(q) · u_01(p - q r) · u_21(r) = [[1,p,q],[0,1,0],[0,r,1]]` (EKL §11, the parametrisation
of `U_(12)`). -/
theorem Upar_step11 (p q r : ℝ) : Work.EKLContract.toMat (Work.EKLContract.uij (show (0 : Fin 3) ≠ 2 by decide) q * Work.EKLContract.uij (show (0 : Fin 3) ≠ 1 by decide) (p - q * r) * Work.EKLContract.uij (show (2 : Fin 3) ≠ 1 by decide) r) = Work.EKLContract.Hmat p q r := by
  simp only [Work.EKLContract.toMat_mul, toMat_uij]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, Work.EKLContract.Hmat, Matrix.mul_apply, Fin.sum_univ_three]

end Work.EKLContract.Lemmas
