import Mathlib

namespace Work.ZeroFreeTables.H4

theorem expTaylorL (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 8/3) :
    Real.exp ((87/250)*t) ≤
      (∑ j ∈ Finset.range 6, ((87/250)*t)^j/(j.factorial:ℝ))
        + ((87/250)*t)^6 * 7 / ((6:ℕ).factorial * 6) := by
  have hx0 : 0 ≤ (87/250 : ℝ) * t := by positivity
  have hx1 : (87/250 : ℝ) * t ≤ 1 := by
    have h2 : (87/250 : ℝ) * (8/3) = 116/125 := by norm_num
    calc (87/250 : ℝ) * t ≤ (87/250) * (8/3) := by
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 116/125 := h2
      _ ≤ 1 := by norm_num
  have h := Real.exp_bound' hx0 hx1 (n := 6) (by norm_num)
  have h7 : ((6 : ℕ) + 1 : ℝ) = 7 := by norm_num
  have h7' : (6 : ℝ) + 1 = 7 := by norm_num
  simp only [h7, h7'] at h
  exact h

end Work.ZeroFreeTables.H4
