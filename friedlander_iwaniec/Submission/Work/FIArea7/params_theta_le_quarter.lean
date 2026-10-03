import Mathlib
import Submission.Work.FITop.Defs

/-!
# `θ ≤ 1/4`

The smoothing parameter of (4.15) is `θ = (log x)^{-A'}` with `A' ≥ 2A + 2^{20}` and `x ≥ 3`.
Since `log x ≥ log 3 > 1 + 1/40`, we have `(log x)^{A'} ≥ (1 + 1/40)^{2^{20}} ≥ 1 + 2^{20}/40 ≥ 4`,
so `θ = ((log x)^{A'})^{-1} ≤ 1/4`.

The numeric input is `log 3 ≥ 1 + 1/40`, obtained from `log 3 = log 2 + log(3/2)` together with
`log 2 > 0.6931471803` (`Real.log_two_gt_d9`) and `log(3/2) ≥ 1/3`
(`Real.log_le_sub_one_of_pos` applied to `2/3`, via `Real.log_inv`).
-/

namespace Work.FIArea7

theorem params_theta_le_quarter (Pa : Work.FITop.Params) : Pa.θ ≤ 1 / 4 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  -- `log 3 ≥ 1 + 1/40`
  have hlog3 : 1 + 1 / 40 ≤ Real.log 3 := by
    have hsplit : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      have h : Real.log (2 * (3 / 2 : ℝ)) = Real.log 2 + Real.log (3 / 2) :=
        Real.log_mul (by norm_num) (by norm_num)
      have h2 : (2 : ℝ) * (3 / 2) = 3 := by norm_num
      rw [h2] at h
      exact h
    have h32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
      have hinv : Real.log (3 / 2) = - Real.log (2 / 3) := by
        rw [show (3 : ℝ) / 2 = (2 / 3)⁻¹ by norm_num, Real.log_inv]
      linarith
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hlogx_ge : 1 + 1 / 40 ≤ Real.log (Pa.x : ℝ) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hx3)
  have hL1 : (1 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
  -- `A' ≥ 2^{20}`
  have hA'ge : ((2 ^ 20 : ℕ) : ℝ) ≤ Pa.A' := by
    have h2 : ((2 : ℝ) ^ 20) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h3 : ((2 ^ 20 : ℕ) : ℝ) = (2 : ℝ) ^ 20 := by norm_num
    linarith
  -- `(log x)^{A'} ≥ 4`
  have key : (4 : ℝ) ≤ Real.log (Pa.x : ℝ) ^ Pa.A' := by
    have h1 : Real.log (Pa.x : ℝ) ^ (((2 ^ 20 : ℕ) : ℝ)) ≤ Real.log (Pa.x : ℝ) ^ Pa.A' :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hL1) hA'ge
    have h2 : Real.log (Pa.x : ℝ) ^ (((2 ^ 20 : ℕ) : ℝ)) = Real.log (Pa.x : ℝ) ^ (2 ^ 20 : ℕ) :=
      Real.rpow_natCast _ _
    have h3 : (1 + 1 / 40 : ℝ) ^ (2 ^ 20 : ℕ) ≤ Real.log (Pa.x : ℝ) ^ (2 ^ 20 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hlogx_ge (2 ^ 20)
    have h4 : (1 : ℝ) + ((2 ^ 20 : ℕ) : ℝ) * (1 / 40) ≤ (1 + 1 / 40 : ℝ) ^ (2 ^ 20 : ℕ) :=
      one_add_mul_le_pow (a := (1 / 40 : ℝ)) (by norm_num) (2 ^ 20)
    have h5 : (4 : ℝ) ≤ (1 : ℝ) + ((2 ^ 20 : ℕ) : ℝ) * (1 / 40) := by norm_num
    calc (4 : ℝ) ≤ 1 + ((2 ^ 20 : ℕ) : ℝ) * (1 / 40) := h5
      _ ≤ (1 + 1 / 40 : ℝ) ^ (2 ^ 20 : ℕ) := h4
      _ ≤ Real.log (Pa.x : ℝ) ^ (2 ^ 20 : ℕ) := h3
      _ = Real.log (Pa.x : ℝ) ^ (((2 ^ 20 : ℕ) : ℝ)) := h2.symm
      _ ≤ Real.log (Pa.x : ℝ) ^ Pa.A' := h1
  rw [Pa.hθ]
  rw [Real.rpow_neg hLpos.le Pa.A']
  exact (by simpa [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 4 by norm_num) key)

end Work.FIArea7
