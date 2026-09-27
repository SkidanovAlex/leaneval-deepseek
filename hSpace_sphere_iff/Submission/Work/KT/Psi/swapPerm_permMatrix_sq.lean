import Mathlib
import Submission.Work.KT.Psi.Basic

namespace Work.KT.Psi

open Equiv

/-- The permutation `swapPerm n` (the swap `(i, j) ↦ (j, i)` of `Fin n × Fin n`) is an
involution: `swapPerm n * swapPerm n = 1`. -/
theorem swapPerm_mul_self (n : ℕ) : swapPerm n * swapPerm n = 1 := by
  ext x
  simp only [Equiv.Perm.mul_apply, swapPerm, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Equiv.prodComm_apply, Prod.swap_swap, Equiv.Perm.one_apply]

/-- The permutation matrix of `swapPerm n` is an involution. -/
theorem swapPerm_permMatrix_sq {A : Type} [Ring A] (n : ℕ) :
    (swapPerm n).permMatrix A * (swapPerm n).permMatrix A = 1 := by
  rw [← Matrix.permMatrix_mul, swapPerm_mul_self, Matrix.permMatrix_one]

end Work.KT.Psi
