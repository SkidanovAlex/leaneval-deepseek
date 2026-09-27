import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- The normalising time `T = ¼|ln κ|` written with the sign of the logarithm stripped off,
for `0 < κ < 1`:  `Tscale κ = -(1/4) * log κ = log (κ^(-1/4))`. -/
theorem Tscale_eq_neg {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tscale κ = -(1 / 4 : ℝ) * Real.log κ := by
  rw [Tscale, abs_of_neg (Real.log_neg hκ0 hκ1)]
  ring

/-- The value of the exponential of the normalisation time: `exp (Tscale κ) = κ^(-1/4)`. -/
theorem exp_Tscale {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Real.exp (Tscale κ) = κ ^ (-(1 / 4) : ℝ) := by
  rw [Tscale_eq_neg hκ0 hκ1]
  have h : -(1 / 4 : ℝ) * Real.log κ = -((1 / 4) * Real.log κ) := by ring
  rw [h, Real.exp_neg, mul_comm (1 / 4 : ℝ) (Real.log κ),
    ← Real.rpow_def_of_pos hκ0 (1 / 4)]
  rw [Real.rpow_neg hκ0.le (1 / 4)]

/-- The key normalisation identity `exp (Tscale κ) * κ = κ^(3/4)` for `0 < κ < 1`. -/
theorem exp_Tscale_mul {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Real.exp (Tscale κ) * κ = κ ^ (3 / 4 : ℝ) := by
  rw [exp_Tscale hκ0 hκ1]
  nth_rewrite 2 [← Real.rpow_one κ]
  rw [← Real.rpow_add hκ0 (-(1 / 4)) 1]
  norm_num

set_option linter.unusedVariables false in
theorem step8_kappa_bound {κ κA κU τ T : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hA0 : 0 ≤ κA) (hU0 : 0 ≤ κU) (hAκ : κA ≤ κ) (hUκ : κU ≤ κ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ T) (hT : T = Tscale κ) :
    max κA (Real.exp τ * κU) ≤ κ ^ (3 / 4 : ℝ) ∧
    κ ^ (3 / 4 : ℝ) = Real.exp T * κ := by
  subst hT
  have hexpκ : Real.exp (Tscale κ) * κ = κ ^ (3 / 4 : ℝ) := exp_Tscale_mul hκ0 hκ1
  -- `κ ≤ κ^(3/4)` because `0 < κ ≤ 1` and `3/4 ≤ 1`.
  have hκ34 : κ ≤ κ ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hκ0 hκ1.le
      (show (3 / 4 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  constructor
  · refine max_le (le_trans hAκ hκ34) ?_
    calc Real.exp τ * κU ≤ Real.exp (Tscale κ) * κ :=
          mul_le_mul (Real.exp_le_exp.mpr hτ1) hUκ hU0 (Real.exp_pos _).le
      _ = κ ^ (3 / 4 : ℝ) := hexpκ
  · exact hexpκ.symm

end Work.EKLC8Core
