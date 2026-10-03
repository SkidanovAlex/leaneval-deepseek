import Mathlib

namespace Work.FIArea4

theorem geom_sum_bound (X : ℕ) {ζ : ℂ} (hζ : ζ ≠ 1) (hζ1 : ‖ζ‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 X, ζ ^ n‖ ≤ 2 / ‖ζ - 1‖ := by
  have h1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  have hpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr h1
  calc ‖∑ n ∈ Finset.Icc 1 X, ζ ^ n‖
      = ‖ζ ^ (X + 1) - ζ‖ / ‖ζ - 1‖ := by
        rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) from
              (Finset.Ico_succ_right_eq_Icc 1 X).symm,
            geom_sum_Ico hζ (m := 1) (n := X + 1) (Nat.le_add_left 1 X),
            pow_one, norm_div]
    _ ≤ (‖ζ ^ (X + 1)‖ + ‖ζ‖) / ‖ζ - 1‖ :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) (le_of_lt hpos)
    _ ≤ 2 / ‖ζ - 1‖ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
        rw [norm_pow]
        have hpow : ‖ζ‖ ^ (X + 1) ≤ 1 := pow_le_one₀ (norm_nonneg ζ) hζ1
        linarith

end Work.FIArea4
