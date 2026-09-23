import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Calculus

/-- For `a < 0` and any real `c`, there is `ε > 0` with `4 * ε * a - 2 * ε ^ 2 * c < 0`. -/
theorem exists_pos_four_mul_sub_sq_mul_neg {a c : ℝ} (ha : a < 0) :
    ∃ ε : ℝ, 0 < ε ∧ 4 * ε * a - 2 * ε ^ 2 * c < 0 := by
  set e : ℝ := -a / (1 + |c|) with he
  have hden : (0 : ℝ) < 1 + |c| := by positivity
  have he_pos : 0 < e := by
    rw [he]
    exact div_pos (neg_pos.mpr ha) hden
  have hfrac : |c| / (1 + |c|) < 1 := by
    rw [div_lt_one hden]
    linarith [abs_nonneg c]
  have he_abs : e * |c| < -a := by
    have h1 : -a * (|c| / (1 + |c|)) < -a := by
      have := mul_lt_mul_of_pos_left hfrac (neg_pos.mpr ha)
      simpa using this
    rw [he]
    have heq : (-a / (1 + |c|)) * |c| = -a * (|c| / (1 + |c|)) := by
      field_simp
    rw [heq]
    exact h1
  have he_c_gt : a < e * c := by
    have h2 : -(e * |c|) ≤ e * c := by
      have h := mul_le_mul_of_nonneg_left (neg_abs_le c) (le_of_lt he_pos)
      rwa [mul_neg] at h
    have h3 : a < -(e * |c|) := by linarith [he_abs]
    linarith [h2, h3]
  refine ⟨e, he_pos, ?_⟩
  have h2a : 2 * a < e * c := by linarith [he_c_gt, ha]
  have key : 4 * e * a - 2 * e ^ 2 * c = 2 * e * (2 * a - e * c) := by ring
  rw [key]
  exact mul_neg_of_pos_of_neg (by linarith [he_pos]) (by linarith [h2a])

end Commons.Analysis.Calculus