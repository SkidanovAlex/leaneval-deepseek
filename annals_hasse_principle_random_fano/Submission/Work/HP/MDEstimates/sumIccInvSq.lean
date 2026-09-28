import Mathlib

namespace Work.HP.MDEstimates

/-- The partial sums of the reciprocals of the squares are bounded above by `2`:
`∑_{l=1}^{N} 1/l² ≤ 2` for every natural number `N`. -/
theorem sumIccInvSq (N : ℕ) : (∑ l ∈ Finset.Icc 1 N, 1 / ((l : ℝ) ^ 2)) ≤ 2 := by
  rcases N with _ | M
  · simp
  · have h1 : Finset.Icc 1 (M + 1) = insert 1 (Finset.Ioo 1 ((M + 1) + 1)) := by
      rw [Finset.Ioo_insert_left (show (1 : ℕ) < (M + 1) + 1 by omega),
        Finset.Ico_add_one_right_eq_Icc]
    rw [h1, Finset.sum_insert (by simp [Finset.mem_Ioo])]
    have hIoo := sum_Ioo_inv_sq_le (α := ℝ) 1 ((M + 1) + 1)
    simp only [one_div] at hIoo ⊢
    norm_num at hIoo ⊢
    linarith

end Work.HP.MDEstimates
