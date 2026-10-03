import Mathlib

namespace Work.KMTPlan.A6

theorem min_le_eight_mul_inv_sq {A ε x : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    min ε (2 * A / (1 + x ^ 2)) ≤ 8 * A / (Real.sqrt (2 * A / ε) + |x|) ^ 2 := by
  have h2A : 0 < 2 * A := by linarith
  have hq : 0 < 2 * A / ε := div_pos h2A hε
  set s : ℝ := Real.sqrt (2 * A / ε) with hs
  -- `s ^ 2 = 2A/ε` is the defining identity; `s > 0`.
  have hs2 : s ^ 2 = 2 * A / ε := by rw [hs]; exact Real.sq_sqrt hq.le
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hq
  have hDpos : 0 < (s + |x|) ^ 2 := by positivity
  have hx0 : 0 ≤ |x| := abs_nonneg x
  -- `ε * s ^ 2 = 2A`
  have hεs : ε * s ^ 2 = 2 * A := by
    rw [hs2]
    field_simp
  rcases le_or_gt |x| s with hx | hx
  · -- Case `|x| ≤ s`: the minimum is at most `ε`, and `(s+|x|)^2 ≤ 4s^2` gives `ε ≤ 8A/(s+|x|)^2`.
    apply le_trans (min_le_left _ _)
    rw [le_div_iff₀ hDpos]
    have hDle : (s + |x|) ^ 2 ≤ 4 * s ^ 2 := by nlinarith [hx, hs0, hx0]
    nlinarith [hεs, hDle, hε.le]
  · -- Case `s < |x|`: the minimum is at most `2A/(1+x^2)`, and `(s+|x|)^2 < 4x^2 ≤ 4(1+x^2)`.
    apply le_trans (min_le_right _ _)
    rw [le_div_iff₀ hDpos]
    have hDle : (s + |x|) ^ 2 ≤ 4 * (1 + x ^ 2) := by
      have h2 : (s + |x|) ^ 2 < 4 * |x| ^ 2 := by nlinarith [hx, hs0, hx0]
      have : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [h2, sq_nonneg x]
    have hmul : (2 * A / (1 + x ^ 2)) * ((s + |x|) ^ 2)
        ≤ (2 * A / (1 + x ^ 2)) * (4 * (1 + x ^ 2)) := by
      apply mul_le_mul_of_nonneg_left hDle
      positivity
    have heq : (2 * A / (1 + x ^ 2)) * (4 * (1 + x ^ 2)) = 8 * A := by
      field_simp
      ring
    linarith [hmul, heq]

end Work.KMTPlan.A6
