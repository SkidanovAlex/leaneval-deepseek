import Mathlib

namespace Work.LinnikAreas.Density4

/-- Reindex the sum over `Icc 2 N` as a sum over `range (N-1)` with the shift `k ↦ k+2`. -/
theorem Icc_two_sum_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, f n) = ∑ k ∈ Finset.range (N - 1), f (k + 2) := by
  have h1 : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have h2 : N + 1 - 2 = N - 1 := by omega
  rw [h1, Finset.sum_Ico_eq_sum_range, h2]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.add_comm 2 k]

end Work.LinnikAreas.Density4
