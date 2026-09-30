import Mathlib
import Submission.Work.BMF.VKChain.log_rpow_third_div
import Submission.Work.BMF.VKChain.kl_prod_num

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- Elementary numeric bound for the KL-range piece: for `M ≤ |t|² + 2`, `1 ≤ M` and
`exp 1000 ≤ |t|`, the Karatsuba–Landau product is at most `1`. -/
theorem kl_prod_le_one {t M : ℝ} (hM1 : 1 ≤ M) (hM : M ≤ |t| ^ 2 + 2) (ht : Real.exp 1000 ≤ |t|) :
    (Real.log M / Real.log 2 + 2) * (24 * Real.pi * M ^ (1 / 3 : ℝ) / |t|) ≤ 1 := by
  set s := |t| with hsdef
  have hspos : 0 < s := lt_of_lt_of_le (Real.exp_pos 1000) ht
  have hs2 : (2:ℝ) ≤ s := by
    have h : (2:ℝ) ≤ Real.exp 1000 := by have := Real.add_one_le_exp 1000; linarith
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hs2sq : (2:ℝ) ≤ s^2 := by nlinarith [hs2]
  have hMs : M ≤ 2 * s^2 := by
    have : s^2 + 2 ≤ 2*s^2 := by nlinarith [hs2sq]
    linarith
  -- `log M ≤ log 2 + 2 log s ≤ 3 log s`
  have hlogM_le : Real.log M ≤ 3*Real.log s := by
    have h1 : Real.log M ≤ Real.log (2*s^2) := Real.log_le_log hMpos hMs
    have h2 : Real.log (2*s^2) = Real.log 2 + 2*Real.log s := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
    have h3 : Real.log 2 ≤ Real.log s := Real.log_le_log (by norm_num) (by linarith)
    rw [h2] at h1; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfac1 : Real.log M / Real.log 2 + 2 ≤ 3 * Real.log s / Real.log 2 + 2 := by
    have : Real.log M / Real.log 2 ≤ 3*Real.log s / Real.log 2 :=
      div_le_div_of_nonneg_right hlogM_le (le_of_lt hlog2pos)
    linarith
  -- `M^{1/3} ≤ (2 s²)^{1/3} = 2^{1/3} s^{2/3} ≤ 2 s^{2/3}`
  have hfac2 : M^(1/3:ℝ) ≤ 2 * s^(2/3:ℝ) := by
    have h1 : M^(1/3:ℝ) ≤ (2*s^2)^(1/3:ℝ) := Real.rpow_le_rpow (le_of_lt hMpos) hMs (by norm_num)
    have h2 : (2*s^2)^(1/3:ℝ) = 2^(1/3:ℝ) * (s^2)^(1/3:ℝ) := Real.mul_rpow (by norm_num) (by positivity)
    have h3 : (s^2)^(1/3:ℝ) = s^(2/3:ℝ) := by
      rw [← Real.rpow_natCast s 2]
      rw [← Real.rpow_mul (le_of_lt hspos) ((2:ℕ):ℝ) (1/3:ℝ)]
      rw [show ((2:ℕ):ℝ)*(1/3:ℝ) = 2/3 by norm_num]
    have h4 : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (show (1:ℝ)/3 ≤ 1 by norm_num)
      simpa [Real.rpow_one] using this
    calc M^(1/3:ℝ) ≤ (2*s^2)^(1/3:ℝ) := h1
      _ = 2^(1/3:ℝ) * (s^2)^(1/3:ℝ) := h2
      _ = 2^(1/3:ℝ) * s^(2/3:ℝ) := by rw [h3]
      _ ≤ 2 * s^(2/3:ℝ) := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (le_of_lt hspos) _)
  -- `s^{2/3}/s = 1/s^{1/3}`
  have h_sdiv : s^(2/3:ℝ)/s = 1/s^(1/3:ℝ) := by
    have hden : s^(2/3:ℝ)/s = s^(2/3:ℝ)/s^(1:ℝ) := by simp only [Real.rpow_one]
    rw [hden, ← Real.rpow_sub hspos (2/3:ℝ) 1]
    rw [show (2/3:ℝ) - 1 = -(1/3) by norm_num]
    rw [Real.rpow_neg (le_of_lt hspos) (1/3), inv_eq_one_div]
  have hstep : 24*Real.pi*M^(1/3:ℝ)/s ≤ 48*Real.pi/s^(1/3:ℝ) := by
    have h1 : 24*Real.pi*M^(1/3:ℝ)/s ≤ 24*Real.pi*(2*s^(2/3:ℝ))/s := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hspos)
      exact mul_le_mul_of_nonneg_left hfac2 (by positivity)
    have h2 : 24*Real.pi*(2*s^(2/3:ℝ))/s = 48*Real.pi/s^(1/3:ℝ) := by
      rw [show 24*Real.pi*(2*s^(2/3:ℝ))/s = 48*Real.pi * (s^(2/3:ℝ)/s) by ring, h_sdiv]
      ring
    exact h1.trans (le_of_eq h2)
  have hlog1000 : (1000:ℝ) ≤ Real.log s := by
    have h := Real.log_le_log (Real.exp_pos 1000) ht
    rwa [Real.log_exp] at h
  have hApos : 0 < s^(1/3:ℝ) := Real.rpow_pos_of_pos hspos _
  have hnum := kl_prod_num (s := s) (A := s^(1/3:ℝ)) hApos (log_rpow_third_div ht) hlog1000
  have hP : (Real.log M / Real.log 2 + 2) * (24*Real.pi*M^(1/3:ℝ)/s) ≤
            (3*Real.log s / Real.log 2 + 2) * (48*Real.pi/s^(1/3:ℝ)) :=
    mul_le_mul hfac1 hstep
      (div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hMpos) _)) (le_of_lt hspos))
      (add_nonneg (div_nonneg (by positivity) (le_of_lt hlog2pos)) (by norm_num))
  linarith [hP, hnum]

end Work.BMF.VKChain
