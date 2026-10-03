import Mathlib
import Submission.Work.Pert.PinLogDev.Helpers
import Submission.Work.Pert.PinLogDev.log_bound_arith

namespace Work.Pert.PinLogDev

/-- The same arithmetic combination as `log_bound_arith`, plus the extra term
`(32/31) * ε * t` with `0 ≤ ε ≤ 1/128`: since `(32/31) * (1/128) = 1/124 < 1/64`, this term is
absorbed by the `t / 64` already present on the right-hand side (and by the `+1` slack in the
constants). -/
theorem log_bound_arith_eps {Ξ Rde C₂ K₁ Kd Kb Cα Y₀ t ε : ℝ}
    (hΞ : 1 + 64 * Real.pi ≤ Ξ) (hRde : 0 < Rde) (hC₂ : 0 ≤ C₂) (hK₁ : 0 ≤ K₁)
    (hKd : 0 ≤ Kd) (hKb : 0 ≤ Kb) (hCα : Ξ + 4 ≤ Cα) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 128)
    (hY : Ξ + 4 * (Rde + C₂ + 2) + 10 ≤ Y₀) (hYt : Y₀ ≤ t) :
    K₁ + Kb + 2 * (Real.sqrt 2 * C₂ *
        (Real.log ((t - Ξ) / (Y₀ - Ξ)) + 2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
      + (32 / 31) * Kd * Real.log (t / Y₀)) + (32 / 31) * ε * t
      ≤ Work.Pert.PinLogDev.Aconst C₂ Kd * Real.log (t + 2)
        + Work.Pert.PinLogDev.Cconst K₁ Kb + t / 64 := by
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hY0Ξ : 18 ≤ Y₀ - Ξ := by linarith
  have hY0Ξpos : 0 < Y₀ - Ξ := by linarith
  have hY0pos : 0 < Y₀ := by linarith
  have htΞpos : 0 < t - Ξ := by linarith
  have htpos : 0 < t := by linarith
  have ht2pos : 0 < t + 2 := by linarith
  have h2Cαpos : 0 < 2 * Cα := by linarith
  have h2Cα10 : 10 ≤ 2 * Cα := by linarith
  have hY0t : 0 ≤ t - Y₀ := by linarith
  have hlog : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  -- (1) log((t-Ξ)/(Y₀-Ξ)) ≤ log(t+2)
  have h1 : Real.log ((t - Ξ) / (Y₀ - Ξ)) ≤ Real.log (t + 2) := by
    apply Real.log_le_log (div_pos htΞpos hY0Ξpos)
    rw [div_le_iff₀ hY0Ξpos]
    have hmul : (t + 2) * 18 ≤ (t + 2) * (Y₀ - Ξ) :=
      mul_le_mul_of_nonneg_left hY0Ξ (le_of_lt ht2pos)
    nlinarith [hmul, hΞ, htpos]
  -- (2) log(1 + (t-Y₀)/(2Cα)) ≤ log(t+2)
  have h2 : Real.log (1 + (t - Y₀) / (2 * Cα)) ≤ Real.log (t + 2) := by
    apply Real.log_le_log ?_ ?_
    · have h := div_nonneg hY0t (by linarith : (0 : ℝ) ≤ 2 * Cα)
      linarith
    · have hdiv : (t - Y₀) / (2 * Cα) ≤ t + 1 := by
        rw [div_le_iff₀ h2Cαpos]
        have hmul : (t + 1) * 10 ≤ (t + 1) * (2 * Cα) :=
          mul_le_mul_of_nonneg_left h2Cα10 (by linarith : (0 : ℝ) ≤ t + 1)
        nlinarith [hmul, hY0t, htpos]
      linarith
  -- (3) log(t/Y₀) ≤ log(t+2)
  have h3 : Real.log (t / Y₀) ≤ Real.log (t + 2) := by
    apply Real.log_le_log (div_pos htpos hY0pos)
    rw [div_le_iff₀ hY0pos]
    have hmul : (t + 2) * 1 ≤ (t + 2) * Y₀ :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Y₀) (le_of_lt ht2pos)
    nlinarith [hmul, htpos]
  -- (4) the extra ε-term is absorbed by `t / 64`, using `(32/31)*(1/128) = 1/124 < 1/64`
  have heps : (32 / 31 : ℝ) * ε * t ≤ t / 64 := by
    have ht0 : 0 ≤ t := le_of_lt htpos
    have hcoef : (32 / 31 : ℝ) * ε ≤ 1 / 64 := by nlinarith [hε, hε0]
    calc (32 / 31 : ℝ) * ε * t ≤ (1 / 64) * t := mul_le_mul_of_nonneg_right hcoef ht0
      _ = t / 64 := by ring
  -- combine, with nonnegative coefficients
  have hD : 0 ≤ Real.sqrt 2 * C₂ := mul_nonneg (Real.sqrt_nonneg 2) hC₂
  have hE : 0 ≤ (32 / 31 : ℝ) * Kd := by
    have : (0 : ℝ) ≤ (32 : ℝ) / 31 := by norm_num
    exact mul_nonneg this hKd
  have e1 : Real.sqrt 2 * C₂ * Real.log ((t - Ξ) / (Y₀ - Ξ))
      ≤ Real.sqrt 2 * C₂ * Real.log (t + 2) := mul_le_mul_of_nonneg_left h1 hD
  have e2 : Real.sqrt 2 * C₂ * (2 * Real.log (1 + (t - Y₀) / (2 * Cα)))
      ≤ Real.sqrt 2 * C₂ * (2 * Real.log (t + 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hD
  have e3 : (32 / 31 : ℝ) * Kd * Real.log (t / Y₀)
      ≤ (32 / 31 : ℝ) * Kd * Real.log (t + 2) := mul_le_mul_of_nonneg_left h3 hE
  rw [Aconst, Cconst]
  nlinarith [e1, e2, e3, heps, hlog, htpos, hK₁, hKb]

end Work.Pert.PinLogDev
