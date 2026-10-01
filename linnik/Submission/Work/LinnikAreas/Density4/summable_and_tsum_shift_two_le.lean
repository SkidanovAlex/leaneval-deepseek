import Mathlib

namespace Work.LinnikAreas.Density4

/-- If a nonnegative sequence `f : ℕ → ℝ` has all its tail partial sums
`∑_{n=2}^{N} f n` bounded by a constant `C`, then `f` is summable and the tail
series `∑' n, f (n + 2)` is bounded by the same `C`.

The proof bounds the partial sums of the shifted nonnegative sequence
`n ↦ f (n + 2)` (they coincide with `∑_{n=2}^{N} f n` up to reindexing), which
gives both summability of the shift and the bound on its `tsum`; summability of
`f` itself follows by shifting the index back. -/
theorem summable_and_tsum_shift_two_le (f : ℕ → ℝ) (hf : ∀ n : ℕ, 0 ≤ f n) (C : ℝ)
    (h : ∀ N : ℕ, 2 ≤ N → (∑ n ∈ Finset.Icc 2 N, f n) ≤ C) :
    Summable f ∧ (∑' n : ℕ, f (n + 2)) ≤ C := by
  -- `C` is nonnegative, being an upper bound for the single term `f 2`.
  have hC : 0 ≤ C := le_trans (hf 2) (by simpa using h 2 le_rfl)
  -- The partial sums of the shifted sequence are exactly the tail partial sums.
  have hidx : ∀ n : ℕ, (∑ k ∈ Finset.range n, f (k + 2)) = ∑ k ∈ Finset.Icc 2 (n + 1), f k := by
    intro n
    have hset : Finset.Icc 2 (n + 1) = Finset.Ico 2 (n + 2) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hset, Finset.sum_Ico_eq_sum_range f 2 (n + 2)]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm]
  -- Hence those partial sums satisfy the same bound `C`.
  have hshift : ∀ n : ℕ, (∑ k ∈ Finset.range n, f (k + 2)) ≤ C := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Finset.range_zero, Finset.sum_empty]
      exact hC
    · rw [hidx n]
      exact h (n + 1) (by omega)
  have hsum_shift : Summable (fun n : ℕ => f (n + 2)) :=
    summable_of_sum_range_le (fun n => hf (n + 2)) hshift
  refine ⟨(summable_nat_add_iff 2).1 hsum_shift, ?_⟩
  exact Real.tsum_le_of_sum_range_le (fun n => hf (n + 2)) hshift

end Work.LinnikAreas.Density4
