import Mathlib

namespace Work.LinnikAreas

/-- Reversed inner sum: `∑_{l<N} g (N - l) = ∑_{m=1}^{N} g m`. -/
lemma sum_range_sub_eq_sum_Icc (g : ℕ → ℝ) (N : ℕ) :
    (∑ l ∈ Finset.range N, g (N - l)) = ∑ m ∈ Finset.Icc 1 N, g m := by
  rw [Finset.range_eq_Ico]
  rw [Finset.sum_Ico_reflect g 0 (m := N) (n := N) (by omega)]
  have h : Finset.Ico (N + 1 - N) (N + 1 - 0) = Finset.Icc 1 N := by
    ext m; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [h]

/-- One-step recurrence for the weighted right-hand side. -/
lemma countTri_rhs_succ (g : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 ((N + 1) - 1), (((N + 1 : ℕ) : ℝ) - m) * g m)
      = (∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m)
        + ∑ m ∈ Finset.Icc 1 N, g m := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
    rw [Nat.add_sub_cancel, hcast]
    have hsplit : (∑ m ∈ Finset.Icc 1 N, ((N : ℝ) - m) * g m)
        = ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m := by
      have hs := Finset.sum_Icc_succ_top (a := 1) (b := N - 1)
        (show 1 ≤ N - 1 + 1 by omega) (fun m => ((N : ℝ) - m) * g m)
      rw [show N - 1 + 1 = N from by omega] at hs
      rw [hs]
      have hz : ((N : ℝ) - (N : ℕ)) * g N = 0 := by ring
      rw [hz, add_zero]
    calc ∑ m ∈ Finset.Icc 1 N, ((N : ℝ) + 1 - m) * g m
        = ∑ m ∈ Finset.Icc 1 N, (((N : ℝ) - m) * g m + g m) := by
            apply Finset.sum_congr rfl; intro m hm; ring
      _ = (∑ m ∈ Finset.Icc 1 N, ((N : ℝ) - m) * g m) + ∑ m ∈ Finset.Icc 1 N, g m := by
            rw [Finset.sum_add_distrib]
      _ = (∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m) + ∑ m ∈ Finset.Icc 1 N, g m := by
            rw [hsplit]

lemma countTri_aux (g : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range k, g (k - l))
      = ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, sum_range_sub_eq_sum_Icc]
    exact (countTri_rhs_succ g N).symm

theorem countTri (g : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range k, g (k - l))
      = ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * g m :=
  countTri_aux g N

end Work.LinnikAreas
