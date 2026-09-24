import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab

/-!
# Numerical helpers for the final assembly (`JR2/NOTES.md`)
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

/-- `e^8 > 2000`. -/
theorem two_thousand_le_exp_eight : (2000:ℝ) ≤ Real.exp 8 := by
  have h2 : (2.7182818283:ℝ)^8 ≤ (Real.exp 1)^8 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
  have h3 : Real.exp 8 = (Real.exp 1)^8 := by
    rw [show (8:ℝ) = ((8:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h3]
  linarith [h2, show ((2.7182818283:ℝ)^8) > 2000 by norm_num]

/-- **The numerical input of the `σ ≤ 2` (Selberg) case**: for `z ≥ e^8` one has
`14251 ≤ z·log z` (since `z ≥ 2000` and `log z ≥ 8`). -/
theorem log2000_le_log {z : ℝ} (hz : Real.exp 8 ≤ z) : (14251:ℝ) ≤ z * Real.log z := by
  have h2000 : (2000:ℝ) ≤ z := le_trans two_thousand_le_exp_eight hz
  have hlog : (8:ℝ) ≤ Real.log z := by
    have h1 := Real.log_le_log (Real.exp_pos 8) hz
    rwa [Real.log_exp] at h1
  have h8 : (0:ℝ) < Real.log z := by linarith
  nlinarith [h2000, hlog, h8]

/-- `2 e^γ < 4`. -/
theorem two_exp_gamma_lt_four : 2 * Real.exp Real.eulerMascheroniConstant < 4 := by
  have h1 : Real.eulerMascheroniConstant < (2:ℝ)/3 := Real.eulerMascheroniConstant_lt_two_thirds
  have h2 : Real.exp Real.eulerMascheroniConstant < Real.exp ((2:ℝ)/3) := Real.exp_lt_exp.mpr h1
  have h3 : Real.exp ((2:ℝ)/3) < 2 := by
    have h4 : Real.exp ((2:ℝ)/3) < Real.exp (Real.log 2) := by
      rw [Real.exp_lt_exp]
      linarith [Real.log_two_gt_d9]
    rwa [Real.exp_log (by norm_num)] at h4
  linarith [h2, h3]

/-- The accumulated sharp error `ε·C₂·errH s ≤ 1/4000` for `ε ≤ min η 1 / 10^11`,
`C₂ = 1000·10100`. -/
theorem sharpness_error_le (ε η : ℝ) (hε0 : 0 ≤ ε) (hεη : ε ≤ min η 1 / 10 ^ 11) (s : ℝ) :
    ε * (1000 * 10100) * errH s ≤ 1 / 4000 := by
  have herrH : errH s ≤ 1 := by
    by_cases h : s ≤ 2
    · rw [errH_of_le_two h, Real.exp_le_one_iff]; norm_num
    · rw [not_le] at h
      by_cases h3 : s ≤ 3
      · rw [errH_of_between h h3, Real.exp_le_one_iff]; linarith
      · rw [not_le] at h3
        rw [errH_of_three_lt h3, div_le_one (by linarith)]
        have h4 : Real.exp (-s) ≤ 1 := by
          rw [Real.exp_le_one_iff]; linarith
        linarith
  have h1 : ε ≤ 1 / 10 ^ 11 := by
    have h2 : min η 1 ≤ 1 := min_le_right _ _
    linarith
  nlinarith [h1, herrH, errH_nonneg s, hε0]

/-- `u₀ := max 2 (exp (K/ε))` satisfies `2 ≤ u₀` and `K ≤ ε log u₀` (for `ε > 0`). -/
theorem u0_bounds (K ε : ℝ) (hε0 : 0 < ε) :
    2 ≤ max 2 (Real.exp (K / ε)) ∧ K ≤ ε * Real.log (max 2 (Real.exp (K / ε))) := by
  refine ⟨le_max_left _ _, ?_⟩
  have h1 : K / ε ≤ Real.log (max 2 (Real.exp (K / ε))) := by
    have h2 : Real.log (Real.exp (K / ε)) ≤ Real.log (max 2 (Real.exp (K / ε))) :=
      Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    rwa [Real.log_exp] at h2
  calc K = ε * (K / ε) := (mul_div_cancel₀ K (ne_of_gt hε0)).symm
    _ ≤ ε * Real.log (max 2 (Real.exp (K / ε))) := mul_le_mul_of_nonneg_left h1 hε0.le

/-- The `σ < 3/2` branch of `Utab`. -/
theorem Utab_of_lt {σ : ℝ} (h : σ < 3/2) :
    Submission.ChenPlan.Utab σ
      = (1005:ℝ)/1000 * (2 * Real.exp Real.eulerMascheroniConstant) / σ := by
  rw [Submission.ChenPlan.Utab, if_pos h]

end

end Work.ChenPlan.LinearSieve.JR2
