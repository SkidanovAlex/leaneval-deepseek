import Mathlib

namespace Work.EKLComp

theorem affine_avg_eventually_lt_succ {q q' c : ℝ} (h : q' < q) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 ≤ n) ∧ q' < ((n : ℝ) * q + c) / ((n : ℝ) + 1) := by
  have hpos : 0 < q - q' := sub_pos.mpr h
  obtain ⟨N, hN⟩ := exists_nat_gt ((q' - c) / (q - q'))
  refine Filter.eventually_atTop.mpr ⟨max N 1, fun n hn => ⟨le_trans (le_max_right _ _) hn, ?_⟩⟩
  have hnN : ((q' - c) / (q - q')) < (n : ℝ) :=
    lt_of_lt_of_le hN (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
  have h1 : q' - c < (n : ℝ) * (q - q') := by
    have := mul_lt_mul_of_pos_right hnN hpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at this
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [h1]

end Work.EKLComp
