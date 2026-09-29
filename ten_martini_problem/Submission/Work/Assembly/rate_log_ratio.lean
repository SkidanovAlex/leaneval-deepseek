import Mathlib

namespace Work.Assembly

/-- From `R ^ (8/9) < (s+1) * Q` with `s ≥ 3` we get
`log (R/s) ≤ log (4/3) + log Q + (1/9) * log R`.

Indeed `s + 1 ≤ (4/3) * s`, so `R^(8/9) < (4/3) * s * Q`; taking logarithms and using
`log (x^y) = y log x` gives `(8/9) log R ≤ log(4/3) + log s + log Q`, which rearranges
to the claim since `log (R/s) = log R - log s`. -/
theorem rate_log_ratio {R Q s : ℝ} (hR : 0 < R) (hQ : 0 < Q) (hs : 3 ≤ s)
    (h : R ^ (8 / 9 : ℝ) < (s + 1) * Q) :
    Real.log (R / s) ≤ Real.log (4 / 3) + Real.log Q + (1 / 9) * Real.log R := by
  have hs0 : 0 < s := by linarith
  -- `s + 1 ≤ (4/3) * s` because `s ≥ 3`
  have hle : R ^ (8 / 9 : ℝ) ≤ (4 / 3 : ℝ) * s * Q := by
    have h2 : (s + 1) * Q ≤ (4 / 3 : ℝ) * s * Q := by nlinarith [hQ]
    linarith [h, h2]
  have hRpos : 0 < R ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hR _
  have h34s : (0 : ℝ) < (4 / 3) * s := by positivity
  -- expand `log ((4/3) * s * Q)`
  have hlogc : Real.log ((4 / 3 : ℝ) * s * Q) =
      Real.log (4 / 3) + Real.log s + Real.log Q := by
    rw [Real.log_mul (ne_of_gt h34s) (ne_of_gt hQ),
      Real.log_mul (by norm_num) (ne_of_gt hs0)]
  have hlog := Real.log_le_log hRpos hle
  rw [Real.log_rpow hR, hlogc] at hlog
  rw [Real.log_div (ne_of_gt hR) (ne_of_gt hs0)]
  nlinarith [hlog]

end Work.Assembly
