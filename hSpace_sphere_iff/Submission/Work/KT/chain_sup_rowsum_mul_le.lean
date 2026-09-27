import Mathlib

namespace Work.KT

/-- The row-sum norm of complex matrices is submultiplicative. -/
theorem chain_sup_rowsum_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (Finset.univ.sup fun i => ∑ j, ‖(A * B) i j‖₊ : NNReal) ≤
      (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) *
        (Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ : NNReal) := by
  apply Finset.sup_le
  intro i _
  calc ∑ k : Fin n, ‖(A * B) i k‖₊
      ≤ ∑ k : Fin n, ∑ j : Fin n, ‖A i j‖₊ * ‖B j k‖₊ := by
        apply Finset.sum_le_sum
        intro k _
        rw [Matrix.mul_apply]
        refine le_trans (nnnorm_sum_le Finset.univ _) ?_
        apply Finset.sum_le_sum
        intro j _
        rw [nnnorm_mul]
    _ = ∑ j : Fin n, ‖A i j‖₊ * (∑ k : Fin n, ‖B j k‖₊) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin n, ‖A i j‖₊ * (Finset.univ.sup fun j => ∑ k, ‖B j k‖₊) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_right
          (Finset.le_sup (s := Finset.univ) (f := fun j => ∑ k, ‖B j k‖₊) (Finset.mem_univ j))
          (‖A i j‖₊)
    _ = (∑ j : Fin n, ‖A i j‖₊) * (Finset.univ.sup fun j => ∑ k, ‖B j k‖₊) := by
        rw [Finset.sum_mul]
    _ ≤ (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) * (Finset.univ.sup fun j => ∑ k, ‖B j k‖₊) := by
        exact mul_le_mul_left
          (Finset.le_sup (s := Finset.univ) (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
          (Finset.univ.sup fun j => ∑ k, ‖B j k‖₊)

end Work.KT
