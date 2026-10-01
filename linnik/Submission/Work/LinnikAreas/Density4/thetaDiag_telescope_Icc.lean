import Mathlib

namespace Work.LinnikAreas.Density4

/-- Telescoping the first differences `H n - H (n+1)` over `n ∈ {2, …, N-1}`
leaves just the endpoint difference `H 2 - H N`. -/
theorem thetaDiag_telescope_Icc (H : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 2 (N-1), (H n - H (n+1)) = H 2 - H N := by
  have hIcc : Finset.Icc 2 (N-1) = Finset.Ico 2 N := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel (by omega : 1 ≤ N)]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  -- Reindex `Ico 2 N` as `range (N-2)` shifted by `2` and telescope backwards.
  have h := Finset.sum_range_sub (fun i : ℕ => H (2 + i)) (N - 2)
  rw [show (2 : ℕ) + (N - 2) = N from by omega, Nat.add_zero] at h
  have hsum : (∑ k ∈ Finset.range (N - 2), (H (2 + k) - H (2 + k + 1)))
      = - ∑ i ∈ Finset.range (N - 2), (H (2 + (i + 1)) - H (2 + i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_assoc (2) k 1]
    ring
  rw [hsum, h]
  ring

end Work.LinnikAreas.Density4
