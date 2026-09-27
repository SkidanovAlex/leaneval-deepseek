import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- `T = Tscale κ = ¼|ln κ|` is at least `5|ln ρ|` when `κ < 2√δ` and `δ < ρ^40/4`.

Indeed `δ < ρ^40/4` forces `2√δ < ρ^20`, hence `κ < ρ^20`; then `ln κ < 20 ln ρ < 0`
and taking absolute values gives `|ln κ| > 20|ln ρ|`, i.e. `T > 5|ln ρ|`. -/
theorem step5_T_ge {ρ δ κ T : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hδ0 : 0 < δ)
    (hδ : δ < ρ ^ 40 / 4) (hκ0 : 0 < κ) (hκ : κ < 2 * δ ^ (1 / 2 : ℝ))
    (hT : T = Tscale κ) : 5 * |Real.log ρ| ≤ T := by
  have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hρ20nonneg : (0 : ℝ) ≤ ρ ^ 20 / 2 := by positivity
  have hsq : ρ ^ 40 / 4 = (ρ ^ 20 / 2) ^ 2 := by ring
  have hsqrt : Real.sqrt (ρ ^ 40 / 4) = ρ ^ 20 / 2 := by
    rw [hsq]; exact Real.sqrt_sq hρ20nonneg
  have hδsqrt : δ ^ (1 / 2 : ℝ) < ρ ^ 20 / 2 := by
    calc δ ^ (1 / 2 : ℝ) = Real.sqrt δ := by rw [Real.sqrt_eq_rpow]
      _ < Real.sqrt (ρ ^ 40 / 4) := Real.sqrt_lt_sqrt (le_of_lt hδ0) hδ
      _ = ρ ^ 20 / 2 := hsqrt
  have hκρ20 : κ < ρ ^ 20 := by
    calc κ < 2 * δ ^ (1 / 2 : ℝ) := hκ
      _ < 2 * (ρ ^ 20 / 2) := by linarith
      _ = ρ ^ 20 := by ring
  have hρ20lt1 : ρ ^ 20 < 1 := by
    have := pow_lt_one₀ hρ0.le hρ1 (by norm_num : (20 : ℕ) ≠ 0)
    simpa using this
  have hκlt1 : κ < 1 := lt_trans hκρ20 hρ20lt1
  have hlogκ : Real.log κ < 0 := Real.log_neg hκ0 hκlt1
  have hlt : Real.log κ < 20 * Real.log ρ := by
    have h := Real.log_lt_log hκ0 hκρ20
    rwa [Real.log_pow] at h
  have hbound : 20 * |Real.log ρ| < |Real.log κ| := by
    rw [abs_of_neg hlogρ, abs_of_neg hlogκ]
    linarith
  rw [hT, Tscale]
  nlinarith [hbound]

end Work.EKLC8Core
