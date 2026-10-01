import Mathlib
import Submission.Work.LinnikAreas.Density4.ThetaLogsumDefs

namespace Work.LinnikAreas.Density4

open MeasureTheory intervalIntegral

/-- On `[n, n+1]` the weight `tgW t = log t + 1` differs from `tgW n` by `log t - log n`,
whose integral is `(n+1) log (1 + 1/n) - 1 = tgEta n`. -/
lemma tgEta_eq_integral (n : ℕ) :
    (∫ t in (n:ℝ)..((n:ℝ)+1), (tgW t - tgW (n:ℝ))) = tgEta n := by
  have hcongr : ∫ t in (n:ℝ)..((n:ℝ)+1), (tgW t - tgW (n:ℝ))
      = ∫ t in (n:ℝ)..((n:ℝ)+1), (Real.log t - Real.log (n:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [tgW]
    ring
  rw [hcongr]
  rw [intervalIntegral.integral_sub intervalIntegrable_log' intervalIntegrable_const]
  rw [integral_log, intervalIntegral.integral_const]
  simp only [tgEta]
  rw [smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    norm_num
  · have hn0 : (n:ℝ) ≠ 0 := by positivity
    have hn1 : (n:ℝ) + 1 ≠ 0 := by positivity
    have hlog : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) = Real.log (1 + 1/(n:ℝ)) := by
      rw [← Real.log_div hn1 hn0]
      congr 1
      field_simp
    have hA : ((n:ℝ)+1) * Real.log ((n:ℝ)+1) - ((n:ℝ)+1) * Real.log (n:ℝ)
        = ((n:ℝ)+1) * Real.log (1 + 1/(n:ℝ)) := by
      rw [← mul_sub, hlog]
    rw [← hA]
    ring

end Work.LinnikAreas.Density4
