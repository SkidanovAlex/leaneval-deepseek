import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# Two `U`-transvections with the same target column multiply to `g`

`g ∈ SL₃(ℝ)` whose matrix agrees with the identity outside the two slots `(i,j)` and `(k,j)`
(where `i`, `j`, `k` are pairwise distinct, so `{i,j,k} = Fin 3`) is the product of the two
elementary transvections it *does* differ in:
`g = u_ij(g_{ij}) · u_kj(g_{kj})`.

This is the `SL₃(ℝ)`-bookkeeping behind the second-order term of the EKL expansion: two root
subgroup elements with the same target index `j` commute, so their product has no cross term.
-/

open Work.EKLContract

namespace Work.EKLContract.Lemmas

/-- `single i j s * single k j t = 0` when `j ≠ k` (the two transvections with the same target
column commute and leave only the two free slots). -/
theorem single_mul_single_same_col_eq_zero {i j k : Fin 3} (hjk : j ≠ k) (s t : ℝ) :
    Matrix.single i j s * Matrix.single k j t = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a ∧ j = x
  · rw [if_pos h1]
    by_cases h2 : k = x ∧ j = b
    · rw [if_pos h2]
      exact absurd (h1.2.trans h2.1.symm) hjk
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

theorem uij_same_target_prod_of_offdiag {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (g : Work.EKLContract.SL3)
    (H : ∀ a b : Fin 3, ¬(a = i ∧ b = j) → ¬(a = k ∧ b = j) →
      Work.EKLContract.toMat g a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) :
    Work.EKLContract.uij hij (Work.EKLContract.toMat g i j) *
      Work.EKLContract.uij hkj (Work.EKLContract.toMat g k j) = g := by
  have hjk : j ≠ k := fun h => hkj h.symm
  have hprod : Matrix.single i j (toMat g i j) * Matrix.single k j (toMat g k j) = 0 :=
    single_mul_single_same_col_eq_zero hjk _ _
  have key : (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j (toMat g i j)
      + Matrix.single k j (toMat g k j)
      = (1 + Matrix.single i j (toMat g i j)) * (1 + Matrix.single k j (toMat g k j)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, hprod, add_zero,
      add_assoc]
  apply Work.EKLContract.ext_toMat
  rw [Work.EKLContract.toMat_mul, horoUij_toMat hij, horoUij_toMat hkj, ← key]
  ext a b
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Matrix.single_apply]
  by_cases h1 : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hij, hik.symm]
  · by_cases h2 : a = k ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hkj, hik]
    · have h1' : ¬(i = a ∧ j = b) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      have h2' : ¬(k = a ∧ j = b) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      rw [if_neg h1', if_neg h2', add_zero, add_zero, ← Matrix.one_apply]
      exact (H a b h1 h2).symm

end Work.EKLContract.Lemmas
