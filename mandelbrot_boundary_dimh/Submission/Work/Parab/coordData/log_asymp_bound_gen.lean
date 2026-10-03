import Mathlib

namespace Work.Parab.coordData

/-- The principal logarithm is an `O(log ‖u‖)` term: there is `c ≥ 0` with
`‖a * log (-u) + b‖ ≤ c * (1 + log (2 + ‖u‖))` for every `u` with `‖u‖ ≥ 1`.
(Suggested `c = ‖a‖ * (1 + π) + ‖b‖ + 1`, from `‖Complex.log z‖ ≤ log ‖z‖ + π` for `z ≠ 0`.) -/
theorem log_asymp_bound_gen (a b : ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ u : ℂ, 1 ≤ ‖u‖ →
      ‖a * Complex.log (-u) + b‖ ≤ c * (1 + Real.log (2 + ‖u‖)) := by
  refine ⟨‖a‖ * (1 + Real.pi) + ‖b‖ + 1, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  -- `‖log z‖ ≤ log ‖z‖ + π` for `‖z‖ ≥ 1`
  have hlog : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
    have h : ‖Complex.log (-u)‖ ≤ |(Complex.log (-u)).re| + |(Complex.log (-u)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im, norm_neg, abs_of_nonneg (Real.log_nonneg hu)] at h
    linarith [Complex.abs_arg_le_pi (-u)]
  -- triangle inequality + the logarithm bound
  have hA : ‖a * Complex.log (-u) + b‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) + ‖b‖ := by
    have h1 := norm_add_le (a * Complex.log (-u)) b
    rw [norm_mul] at h1
    have h2 : ‖a‖ * ‖Complex.log (-u)‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) :=
      mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
    linarith
  have hLnn : 0 ≤ Real.log (2 + ‖u‖) := Real.log_nonneg (by linarith)
  have hlogu : Real.log ‖u‖ ≤ Real.log (2 + ‖u‖) := Real.log_le_log hu0 (by linarith)
  -- `log ‖u‖ + π ≤ (1 + π) * (1 + log (2 + ‖u‖))`
  have hs1 : Real.log ‖u‖ + Real.pi ≤ (1 + Real.pi) * (1 + Real.log (2 + ‖u‖)) := by
    have hpiL : 0 ≤ Real.pi * Real.log (2 + ‖u‖) := mul_nonneg Real.pi_pos.le hLnn
    nlinarith
  have h1 : ‖a‖ * (Real.log ‖u‖ + Real.pi) ≤
      (‖a‖ * (1 + Real.pi)) * (1 + Real.log (2 + ‖u‖)) := by
    calc ‖a‖ * (Real.log ‖u‖ + Real.pi)
        ≤ ‖a‖ * ((1 + Real.pi) * (1 + Real.log (2 + ‖u‖))) :=
          mul_le_mul_of_nonneg_left hs1 (norm_nonneg a)
      _ = (‖a‖ * (1 + Real.pi)) * (1 + Real.log (2 + ‖u‖)) := by ring
  have h2 : ‖b‖ ≤ (‖b‖ + 1) * (1 + Real.log (2 + ‖u‖)) := by
    have hbL : 0 ≤ ‖b‖ * Real.log (2 + ‖u‖) := mul_nonneg (norm_nonneg b) hLnn
    nlinarith
  have hsum := add_le_add h1 h2
  have heq : (‖a‖ * (1 + Real.pi)) * (1 + Real.log (2 + ‖u‖))
        + (‖b‖ + 1) * (1 + Real.log (2 + ‖u‖))
      = (‖a‖ * (1 + Real.pi) + ‖b‖ + 1) * (1 + Real.log (2 + ‖u‖)) := by ring
  linarith

end Work.Parab.coordData
