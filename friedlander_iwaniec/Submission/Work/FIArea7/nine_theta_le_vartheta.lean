import Mathlib
import Submission.Work.FITop.Defs

/-!
# `9 θ ≤ ϑ`

The smoothing parameter `θ = (log x)^{-A'}` (4.15) is at least `9` times *smaller* than the
saving factor `ϑ = (log x)^{-A}` (4.16), because `A' ≥ 2A + 2^{20}` and `log x ≥ log 3 > 41/40 > 1`:
with `L = log x`,

  `L^{A' - A} ≥ L^{2^{20}} ≥ (41/40)^{2^{20}} ≥ 1 + 2^{20}/40 > 9`,

so multiplying `9 ≤ L^{A' - A}` by `L^{A} > 0` gives `9 L^{A} ≤ L^{A'}`, i.e. `9 θ ≤ ϑ`.

The numeric input `log 3 ≥ 1 + 1/40` is obtained from `log 3 = log 2 + log(3/2)` together with
`log 2 > 0.6931471803` (`Real.log_two_gt_d9`) and `log(3/2) ≥ 1/3`
(`Real.log_le_sub_one_of_pos` applied to `2/3`, via `Real.log_inv`).
-/

namespace Work.FIArea7

theorem nine_theta_le_vartheta (Pa : Work.FITop.Params) : 9 * Pa.θ ≤ Pa.ϑ := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
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
  have hLge : 1 + 1 / 40 ≤ Real.log (Pa.x : ℝ) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hx3)
  have hL1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
  -- `A' - A ≥ 2^{20}`
  have hdiff : ((2 ^ 20 : ℕ) : ℝ) ≤ Pa.A' - Pa.A := by
    have h3 : ((2 ^ 20 : ℕ) : ℝ) = (2 : ℝ) ^ 20 := by norm_num
    have h : ((2 : ℝ) ^ 20) ≤ Pa.A' - Pa.A := by linarith [Pa.hA', Pa.hA]
    linarith
  -- `9 ≤ (log x)^{A' - A}`
  have hKey : (9 : ℝ) ≤ Real.log (Pa.x : ℝ) ^ (Pa.A' - Pa.A) := by
    have h1 : Real.log (Pa.x : ℝ) ^ (((2 ^ 20 : ℕ) : ℝ)) ≤ Real.log (Pa.x : ℝ) ^ (Pa.A' - Pa.A) :=
      Real.rpow_le_rpow_of_exponent_le hL1 hdiff
    have h2 : Real.log (Pa.x : ℝ) ^ (((2 ^ 20 : ℕ) : ℝ)) = Real.log (Pa.x : ℝ) ^ (2 ^ 20 : ℕ) :=
      Real.rpow_natCast _ _
    have h3 : (1 + 1 / 40 : ℝ) ^ (2 ^ 20 : ℕ) ≤ Real.log (Pa.x : ℝ) ^ (2 ^ 20 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hLge (2 ^ 20)
    have h4 : (1 : ℝ) + ((2 ^ 20 : ℕ) : ℝ) * (1 / 40) ≤ (1 + 1 / 40 : ℝ) ^ (2 ^ 20 : ℕ) :=
      one_add_mul_le_pow (a := (1 / 40 : ℝ)) (by norm_num) (2 ^ 20)
    have h5 : (9 : ℝ) ≤ (1 : ℝ) + ((2 ^ 20 : ℕ) : ℝ) * (1 / 40) := by norm_num
    calc (9 : ℝ) ≤ 1 + ((2 ^ 20 : ℕ) : ℝ) * (1 / 40) := h5
      _ ≤ (1 + 1 / 40 : ℝ) ^ (2 ^ 20 : ℕ) := h4
      _ ≤ Real.log (Pa.x : ℝ) ^ (2 ^ 20 : ℕ) := h3
      _ = Real.log (Pa.x : ℝ) ^ (((2 ^ 20 : ℕ) : ℝ)) := h2.symm
      _ ≤ Real.log (Pa.x : ℝ) ^ (Pa.A' - Pa.A) := h1
  have hKA'pos : (0 : ℝ) < Real.log (Pa.x : ℝ) ^ Pa.A' := Real.rpow_pos_of_pos hLpos _
  -- Substitute `θ`, `ϑ` and clear the common positive factor `(log x)^{A'}`.
  rw [Pa.hθ, Pa.hϑ]
  have hl : Real.log (Pa.x : ℝ) ^ (-Pa.A') * Real.log (Pa.x : ℝ) ^ Pa.A' = 1 := by
    rw [← Real.rpow_add hLpos, neg_add_cancel, Real.rpow_zero]
  have hr : Real.log (Pa.x : ℝ) ^ (-Pa.A) * Real.log (Pa.x : ℝ) ^ Pa.A'
      = Real.log (Pa.x : ℝ) ^ (Pa.A' - Pa.A) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  have hstep : (9 * Real.log (Pa.x : ℝ) ^ (-Pa.A')) * Real.log (Pa.x : ℝ) ^ Pa.A'
      ≤ Real.log (Pa.x : ℝ) ^ (-Pa.A) * Real.log (Pa.x : ℝ) ^ Pa.A' := by
    rw [mul_assoc, hl, mul_one, hr]
    exact hKey
  exact le_of_mul_le_mul_right hstep hKA'pos

end Work.FIArea7
