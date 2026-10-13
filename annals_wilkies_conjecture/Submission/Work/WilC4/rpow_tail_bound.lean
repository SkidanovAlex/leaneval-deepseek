import Mathlib

namespace Work.WilC4

theorem rpow_tail_bound {q : ℚ} {a : ℝ} (ha : a ≠ 0) {R₁ : ℝ} {P : ℝ → ℝ → Prop}
    (h : ∀ x y : ℝ, R₁ ≤ x → P x y → |y / x ^ (q : ℝ) - a| < |a| / 2) :
    ∃ N : ℕ, ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → P x y → |y| ≤ x ^ N := by
  -- Choose a natural number `N` with `q + 1 ≤ N`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (q : ℝ) + 1 ≤ (N : ℝ) := exists_nat_ge ((q : ℝ) + 1)
  refine ⟨N, max (max R₁ 1) (3 * |a| / 2), ?_⟩
  intro x y hx hP
  have hxR1 : R₁ ≤ x := le_trans (le_trans (le_max_left R₁ 1) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right R₁ 1) (le_max_left _ _)) hx
  have hxA : 3 * |a| / 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxp : 0 < x ^ (q : ℝ) := Real.rpow_pos_of_pos hxpos _
  have h1 : |y / x ^ (q : ℝ) - a| < |a| / 2 := h x y hxR1 hP
  -- `|y / x ^ q|` is bounded by `3 * |a| / 2`.
  have h2 : |y / x ^ (q : ℝ)| < 3 * |a| / 2 := by
    have h3 : |(y / x ^ (q : ℝ) - a) + a| ≤ |y / x ^ (q : ℝ) - a| + |a| := abs_add_le _ _
    have h4 : (y / x ^ (q : ℝ) - a) + a = y / x ^ (q : ℝ) := by ring
    rw [h4] at h3
    linarith
  -- Hence `|y| < (3 * |a| / 2) * x ^ q`.
  have h3 : |y| < 3 * |a| / 2 * x ^ (q : ℝ) := by
    have hy : y = y / x ^ (q : ℝ) * x ^ (q : ℝ) := by
      rw [div_mul_cancel₀ _ (ne_of_gt hxp)]
    rw [hy, abs_mul, abs_of_pos hxp]
    exact mul_lt_mul_of_pos_right h2 hxp
  -- Since `x ≥ 3 * |a| / 2` and `x ≥ 1`, `(3 * |a| / 2) * x ^ q ≤ x ^ (q + 1) ≤ x ^ N`.
  have h4 : 3 * |a| / 2 * x ^ (q : ℝ) ≤ x ^ N := by
    have h5 : 3 * |a| / 2 * x ^ (q : ℝ) ≤ x * x ^ (q : ℝ) :=
      mul_le_mul_of_nonneg_right hxA (le_of_lt hxp)
    have h6 : x * x ^ (q : ℝ) = x ^ (1 + (q : ℝ)) := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    rw [h6] at h5
    have h7 : x ^ (1 + (q : ℝ)) ≤ x ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_natCast] at h7
    linarith
  linarith

end Work.WilC4
