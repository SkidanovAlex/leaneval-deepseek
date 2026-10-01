import Mathlib

namespace Work.LinnikAreas.Density4

/-- For `u ≥ 0`, `u ^ 7 * e ^ (-u) ≤ 5040 = 7!`, obtained from the Taylor bound
`e ^ u ≥ u ^ 7 / 7!`. -/
lemma pow_seven_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 7 * Real.exp (-u) ≤ 5040 := by
  have h := Real.pow_div_factorial_le_exp u hu 7
  norm_num at h
  have hE : 0 < Real.exp (-u) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right h hE.le
  have h1 : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h1] at hmul
  nlinarith [hmul]

/-- Bound of a sixth-power times an exponential: for `c > 0` and `t ≥ 0`,
`8 t ^ 6 (1 + t) e ^ (-(c t))` is bounded by the maximum of the two natural
branch estimates. -/
theorem exp_six_bound {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 0 ≤ t) :
    8 * t ^ 6 * (1 + t) * Real.exp (-(c * t)) ≤ max (16 * 5040 / c ^ 7) 16 := by
  have hcp : (0:ℝ) < c ^ 7 := pow_pos hc 7
  have hE : 0 ≤ Real.exp (-(c * t)) := (Real.exp_pos _).le
  by_cases h1 : (1:ℝ) ≤ t
  · -- large `t`: use `1 + t ≤ 2 t` and `(c t) ^ 7 e ^ (-(c t)) ≤ 5040`.
    have h2 : 1 + t ≤ 2 * t := by linarith
    have step1 : 8 * t ^ 6 * (1 + t) ≤ 16 * t ^ 7 := by
      calc 8 * t ^ 6 * (1 + t) ≤ 8 * t ^ 6 * (2 * t) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 16 * t ^ 7 := by ring
    have step2 := mul_le_mul_of_nonneg_right step1 hE
    have hu : 0 ≤ c * t := mul_nonneg hc.le ht
    have h7 := pow_seven_mul_exp_neg_le hu
    have ht7 : t ^ 7 * Real.exp (-(c * t)) ≤ 5040 / c ^ 7 := by
      have heq : t ^ 7 * Real.exp (-(c * t)) = ((c*t)^7 * Real.exp (-(c*t))) / c^7 := by
        rw [eq_div_iff (ne_of_gt hcp)]
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right h7 hcp.le
    calc 8 * t ^ 6 * (1 + t) * Real.exp (-(c * t))
        ≤ 16 * t ^ 7 * Real.exp (-(c * t)) := step2
      _ = 16 * (t ^ 7 * Real.exp (-(c * t))) := by ring
      _ ≤ 16 * (5040 / c ^ 7) := mul_le_mul_of_nonneg_left ht7 (by norm_num)
      _ = 16 * 5040 / c ^ 7 := by ring
      _ ≤ max (16 * 5040 / c ^ 7) 16 := le_max_left _ _
  · -- small `t`: everything is bounded by the cruder constant `16`.
    have ht1 : t ≤ 1 := by linarith [not_le.mp h1]
    have ht6 : t ^ 6 ≤ 1 := pow_le_one₀ ht ht1
    have h2 : 1 + t ≤ 2 := by linarith
    have hE1 : Real.exp (-(c * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg hc.le ht]
    calc 8 * t ^ 6 * (1 + t) * Real.exp (-(c * t))
        ≤ 8 * 1 * 2 * 1 := by gcongr
      _ = 16 := by norm_num
      _ ≤ max (16 * 5040 / c ^ 7) 16 := le_max_right _ _

end Work.LinnikAreas.Density4
