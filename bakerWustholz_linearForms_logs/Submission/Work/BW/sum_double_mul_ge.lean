import Mathlib
import Submission.Work.BW.mvdefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem sum_double_mul_ge {s : Finset ℕ} {m n : ℕ} (w : ℕ → ℝ) (U : Fin m → ℕ → ℝ) (V : Fin n → ℕ → ℝ)
    (C : Fin m → Fin n → ℝ) (h : ∀ i j, C i j ≤ ∑ k ∈ s, w k * (U i k * V j k)) :
    ∑ i, ∑ j, C i j ≤ ∑ k ∈ s, w k * (∑ i, U i k) * (∑ j, V j k) := by
  have h2 : (∑ i, ∑ j, ∑ k ∈ s, w k * (U i k * V j k))
      = ∑ k ∈ s, w k * (∑ i, U i k) * (∑ j, V j k) := by
    symm
    calc (∑ k ∈ s, w k * (∑ i, U i k) * (∑ j, V j k))
        = ∑ k ∈ s, ∑ i, ∑ j, w k * (U i k * V j k) := by
          apply Finset.sum_congr rfl
          intro k _
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ k ∈ s, w k * (U i k * V j k) := by
          rw [Finset.sum_comm (s := s) (t := Finset.univ)]
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
  calc ∑ i, ∑ j, C i j
      ≤ ∑ i, ∑ j, ∑ k ∈ s, w k * (U i k * V j k) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact h i j
    _ = ∑ k ∈ s, w k * (∑ i, U i k) * (∑ j, V j k) := h2

end Work.BW
