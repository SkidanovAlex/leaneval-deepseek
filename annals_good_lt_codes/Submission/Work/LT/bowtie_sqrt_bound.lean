import Mathlib

namespace Work.LT

/-- Quadratic core of the bow-tie estimate.

If `t² ≤ 4 ε t + 4 ε²` with `ε ≥ 0`, then `t ≤ (2 + 2√2) ε`.
Equivalently `(t - 2ε)² ≤ 8ε²`, so `|t - 2ε| ≤ 2√2 ε` and hence
`t ≤ 2ε + 2√2 ε`. -/
lemma sq_le_four_mul_add_sqrt_two (t ε : ℝ) (hε : 0 ≤ ε)
    (h : t ^ 2 ≤ 4 * ε * t + 4 * ε ^ 2) :
    t ≤ (2 + 2 * Real.sqrt 2) * ε := by
  have hr2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hA0 : 0 ≤ 2 * Real.sqrt 2 * ε := by positivity
  -- `(t - 2ε)² = t² - 4εt + 4ε² ≤ 8ε² = (2√2 ε)²`
  have hsq : (t - 2 * ε) ^ 2 ≤ (2 * Real.sqrt 2 * ε) ^ 2 := by
    rw [mul_pow, mul_pow, hr2]; ring_nf
    nlinarith [h]
  have h1 : |t - 2 * ε| ≤ 2 * Real.sqrt 2 * ε := by
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hA0] at this
  nlinarith [(abs_le.mp h1).2]

/-- Bow-tie arithmetic bound: from `u ≤ 4 ε √u + 4 ε²` with `u, ε ≥ 0`
conclude `u ≤ (2 + 2√2)² ε²`. -/
theorem bowtie_sqrt_bound (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (h : u ≤ 4 * ε * Real.sqrt u + 4 * ε ^ 2) :
    u ≤ (2 + 2 * Real.sqrt 2) ^ 2 * ε ^ 2 := by
  have ht0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hu2 : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
  -- rewrite the hypothesis as a quadratic inequality in `t = √u`
  have h' : (Real.sqrt u) ^ 2 ≤ 4 * ε * (Real.sqrt u) + 4 * ε ^ 2 := by
    rw [hu2]; exact h
  have hb := sq_le_four_mul_add_sqrt_two (Real.sqrt u) ε hε h'
  have hfin : u ≤ ((2 + 2 * Real.sqrt 2) * ε) ^ 2 := by
    rw [← hu2]
    exact pow_le_pow_left₀ ht0 hb 2
  calc u ≤ ((2 + 2 * Real.sqrt 2) * ε) ^ 2 := hfin
    _ = (2 + 2 * Real.sqrt 2) ^ 2 * ε ^ 2 := by ring

end Work.LT
