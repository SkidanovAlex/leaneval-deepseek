import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower

namespace Work.LinnikAreas.Zeta1Aux

/-- **Jensen-type numerator bound for `ζ₁` on the line `Re s = 2`.**

Since `‖ζ₁ (2 + i t)‖ ≥ 1/4` (`Commons.NumberTheory.Zeta.zeta1_re_two_lower`) the
numerator inside the logarithm is bounded above by
`4 · Cbig · (|t| + 9)^13`, whose logarithm is at most
`log 4 + log Cbig + 13 log(|t| + 9)`; using `|t| + 9 ≤ 3(|t| + 3)` and
`log(|t| + 3) ≥ 1` this is dominated by
`(log 4 + log Cbig + 13 log 3 + 13) · log(|t| + 3)`.  Dividing by the positive
constant `log(4/(37/10)) = log(40/37)` yields the claim. -/
theorem zeta1_jensenBound_le {Cbig t : ℝ} (hCbig : 1 ≤ Cbig) (ht : 5 ≤ |t|) :
    Real.log (Cbig * (|t| + 9) ^ 13 / ‖riemannZeta₁ ((2 : ℂ) + Complex.I * (t : ℂ))‖) /
        Real.log (4 / (37 / 10))
      ≤ ((Real.log 4 + Real.log Cbig + 13 * Real.log 3 + 13) / Real.log (4 / (37 / 10))) *
          Real.log (|t| + 3) := by
  set ζ : ℂ := riemannZeta₁ ((2 : ℂ) + Complex.I * (t : ℂ)) with hζ
  have hXpos : 0 < |t| + 9 := by positivity
  have hYpos : 0 < |t| + 3 := by positivity
  have hCpos : 0 < Cbig := by linarith
  have hζlow : (1 / 4 : ℝ) ≤ ‖ζ‖ := by
    rw [hζ]; exact Commons.NumberTheory.Zeta.zeta1_re_two_lower t
  have hζne : ‖ζ‖ ≠ 0 := by
    intro h; rw [h] at hζlow; norm_num at hζlow
  have hnumpos : 0 < Cbig * (|t| + 9) ^ 13 := by positivity
  have hpowpos : (0 : ℝ) < (|t| + 9) ^ 13 := by positivity
  have hL1 : 1 ≤ Real.log (|t| + 3) := by
    have hexp : Real.exp 1 ≤ |t| + 3 := by
      have he := Real.exp_one_lt_three
      have h0 : (0 : ℝ) ≤ |t| := abs_nonneg t
      linarith
    exact (Real.le_log_iff_exp_le hYpos).mpr hexp
  have hA0 : 0 ≤ Real.log 4 + Real.log Cbig + 13 * Real.log 3 := by
    have h1 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log Cbig := Real.log_nonneg hCbig
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  have hbound : Real.log (Cbig * (|t| + 9) ^ 13 / ‖ζ‖) ≤
      (Real.log 4 + Real.log Cbig + 13 * Real.log 3 + 13) * Real.log (|t| + 3) := by
    have hsplit : Real.log (Cbig * (|t| + 9) ^ 13 / ‖ζ‖) =
        Real.log (Cbig * (|t| + 9) ^ 13) - Real.log ‖ζ‖ :=
      Real.log_div (ne_of_gt hnumpos) hζne
    have h1 : Real.log (Cbig * (|t| + 9) ^ 13) = Real.log Cbig + 13 * Real.log (|t| + 9) := by
      rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt hpowpos), Real.log_pow]
      norm_num
    have h2 : Real.log (|t| + 9) ≤ Real.log 3 + Real.log (|t| + 3) := by
      have hle : |t| + 9 ≤ 3 * (|t| + 3) := by
        have h0 : (0 : ℝ) ≤ |t| := abs_nonneg t
        linarith
      calc Real.log (|t| + 9) ≤ Real.log (3 * (|t| + 3)) := Real.log_le_log hXpos hle
        _ = Real.log 3 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (ne_of_gt hYpos)
    have h3 : Real.log (1 / 4) ≤ Real.log ‖ζ‖ := Real.log_le_log (by norm_num) hζlow
    have h4 : Real.log (1 / 4) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    rw [hsplit, h1]
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hL1)]
  have hdpos : 0 < Real.log (4 / (37 / 10)) := Real.log_pos (by norm_num)
  calc Real.log (Cbig * (|t| + 9) ^ 13 / ‖ζ‖) / Real.log (4 / (37 / 10))
      ≤ ((Real.log 4 + Real.log Cbig + 13 * Real.log 3 + 13) * Real.log (|t| + 3)) /
          Real.log (4 / (37 / 10)) :=
        div_le_div_of_nonneg_right hbound (le_of_lt hdpos)
    _ = ((Real.log 4 + Real.log Cbig + 13 * Real.log 3 + 13) / Real.log (4 / (37 / 10))) *
          Real.log (|t| + 3) := by ring

end Work.LinnikAreas.Zeta1Aux
