import Mathlib

namespace Work.Parab.coverCone

/-- For every positive `c`, `Real.log t ≤ c * t` for all sufficiently large `t`.
This follows from `Real.log =o[atTop] id` (log is little-o of the identity),
which yields an eventual bound `Real.log t ≤ c * t`. -/
theorem log_le_mul (c : ℝ) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → Real.log t ≤ c * t := by
  have h : ∀ᶠ t in Filter.atTop, Real.log t ≤ c * t := by
    filter_upwards [Real.isLittleO_log_id_atTop.bound hc,
      Filter.eventually_ge_atTop (1 : ℝ)] with t ht ht1
    simp only [id_eq, Real.norm_eq_abs] at ht
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t),
      abs_of_nonneg (Real.log_nonneg ht1)] at ht
    exact ht
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 h
  exact ⟨max T 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun t ht => hT t (le_trans (le_max_left _ _) ht)⟩

end Work.Parab.coverCone
