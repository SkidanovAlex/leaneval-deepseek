import Mathlib
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

open Work.EKLContract

/-- The root-group transvections `u_ij(a) = 1 + a E_ij` and `u_kl(s) = 1 + s E_kl` commute
whenever `j ≠ k` and `l ≠ i`: at the level of the elementary matrices both cross products
`E_ij E_kl` and `E_kl E_ij` vanish, so the product expands to `1 + a E_ij + s E_kl` both ways. -/
theorem uij_commute {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a s : ℝ) :
    Work.EKLContract.uij hij a * Work.EKLContract.uij hkl s
      = Work.EKLContract.uij hkl s * Work.EKLContract.uij hij a := by
  have hAB : Matrix.single i j a * Matrix.single k l s = 0 :=
    Matrix.single_mul_single_of_ne a i j k hjk s
  have hBA : Matrix.single k l s * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne s k l i hli a
  apply ext_toMat
  simp only [toMat_mul, Work.EKLContract.Lemmas.horoUij_toMat hij a,
    Work.EKLContract.Lemmas.horoUij_toMat hkl s]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hAB, hBA]
  abel

/-- `u_ij(a)` normalises `u_kl(s)` whenever the two root groups are "opposite enough"
(`j ≠ k`, `l ≠ i`); in that case they actually commute. -/
theorem uij_normalizes_uij {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a s : ℝ) :
    Work.EKLContract.uij hij a * Work.EKLContract.uij hkl s * (Work.EKLContract.uij hij a)⁻¹
      = Work.EKLContract.uij hkl s := by
  rw [uij_commute hij hkl hjk hli a s, mul_assoc, mul_inv_cancel, mul_one]

end Work.EKLC6Core
