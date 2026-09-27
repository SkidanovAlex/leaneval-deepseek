import Mathlib

namespace Work.EKLComp

/-- For `q' < q`, the affine average `(((n:ℝ)+1) * q - c) / n` is eventually greater
than `q'` (it tends to `q` as `n → ∞`), for all sufficiently large `n ≥ 1`. -/
theorem affine_avg_eventually_lt_pred {q q' c : ℝ} (h : q' < q) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 ≤ n) ∧ q' < (((n : ℝ) + 1) * q - c) / (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((c - q) / (q - q'))
  have hd : 0 < q - q' := sub_pos.mpr h
  have hN' : c - q < (N : ℝ) * (q - q') := by
    have := mul_lt_mul_of_pos_right hN hd
    rwa [div_mul_cancel₀ _ hd.ne'] at this
  rw [Filter.eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℕ) ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  refine ⟨hn1, ?_⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hle : (N : ℝ) * (q - q') ≤ (n : ℝ) * (q - q') :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) (le_of_lt hd)
  rw [lt_div_iff₀ hnpos]
  nlinarith [hN', hle]

end Work.EKLComp
