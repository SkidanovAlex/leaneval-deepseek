import Mathlib

namespace Work.BourgainPlan.Maximal

/-- The blocks `m' * N + {0, ..., N-1}` for `m' < M` partition `{0, ..., M*N-1}`. -/
lemma sum_block_eq_sum_range (c : ℕ → ℝ) (M N : ℕ) :
    ∑ m' ∈ Finset.range M, ∑ k ∈ Finset.range N, c (m' * N + k)
      = ∑ k ∈ Finset.range (M * N), c k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

theorem sum_block_sq_le (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (M N : ℕ) :
    ∑ m' ∈ Finset.range M, (∑ k ∈ Finset.range N, c (m' * N + k)) ^ 2
      ≤ (∑ k ∈ Finset.range (M * N), c k) ^ 2 := by
  have hsplit := sum_block_eq_sum_range c M N
  rw [← hsplit]
  exact Finset.sum_sq_le_sq_sum_of_nonneg
    (fun m' _ => Finset.sum_nonneg fun k _ => hc _)

end Work.BourgainPlan.Maximal
