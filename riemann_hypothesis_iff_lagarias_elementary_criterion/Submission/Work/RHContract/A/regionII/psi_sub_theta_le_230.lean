import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt

/-!
# `ψ ξ − θ ξ ≤ 2.3 √ξ` for `ξ ≥ 30000`

The Costa–Pereira inequality bounds the difference of the Chebyshev functions by

`ψ ξ − θ ξ ≤ ψ(ξ^{1/2}) + ψ(ξ^{1/3}) + ψ(ξ^{1/5})`,

and the elementary linear bound `ψ y ≤ (log 3) · y` (Hanson's bound on `lcm(1,…,n)`, available
as `Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real`) turns the right hand side into

`(log 3) · (ξ^{1/2} + ξ^{1/3} + ξ^{1/5})`.

For `ξ ≥ 30000` the two higher-power terms are small multiples of `ξ^{1/2}`:
`ξ^{1/3} ≤ (1/4) ξ^{1/2}` (since `ξ ≥ 4^6 = 4096`) and `ξ^{1/5} ≤ (1/4) ξ^{1/2}`
(since `ξ ≥ 128 ≥ 4^{10/3}`).  Altogether

`ψ ξ − θ ξ ≤ (log 3) · (3/2) · ξ^{1/2} ≤ (3/2 log 3) √ξ ≤ 2.3 √ξ`,

because `log 3 < 1.0986122888` gives `(3/2) log 3 < 1.648`.
-/

namespace Work.RHContract.A.regionII

/-- For `x ≥ 4^6 = 4096`, `x^{1/3} ≤ (1/4) x^{1/2}`.  Equivalently `4 ≤ x^{1/6}`. -/
private lemma rpow_third_le_quarter {x : ℝ} (hx : 4096 ≤ x) :
    x ^ (1 / 3 : ℝ) ≤ (1 / 4) * x ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h4096 : (4096 : ℝ) ^ (1 / 6 : ℝ) = 4 := by
    have h := Real.pow_rpow_inv_natCast (x := (4 : ℝ)) (n := 6) (by norm_num) (by norm_num)
    rwa [show (((6 : ℕ) : ℝ))⁻¹ = (1 / 6 : ℝ) by norm_num,
         show ((4 : ℝ) ^ 6) = (4096 : ℝ) by norm_num] at h
  have h4 : (4 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ 4096 by norm_num) hx
      (show (0 : ℝ) ≤ 1 / 6 by norm_num)
    rwa [h4096] at h
  have hhalf : x ^ (1 / 2 : ℝ) = x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hmain : (4 : ℝ) * x ^ (1 / 3 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hx0.le _)
  linarith [hmain]

/-- For `x ≥ 128 ≥ 4^{10/3}`, `x^{1/5} ≤ (1/4) x^{1/2}`.  Equivalently `4 ≤ x^{3/10}`. -/
private lemma rpow_fifth_le_quarter {x : ℝ} (hx : 128 ≤ x) :
    x ^ (1 / 5 : ℝ) ≤ (1 / 4) * x ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hbase : (4 : ℝ) ^ (10 / 3 : ℝ) ≤ 128 := by
    rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) _)
      (show (0 : ℝ) ≤ 128 by norm_num) (show (0 : ℝ) < 3 by norm_num)]
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 4 by norm_num), show (10 / 3 : ℝ) * 3 = 10 by norm_num]
    norm_num
  have h4 : (4 : ℝ) ≤ x ^ (3 / 10 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) _)
      (le_trans hbase hx) (show (0 : ℝ) ≤ 3 / 10 by norm_num)
    rwa [show ((4 : ℝ) ^ (10 / 3 : ℝ)) ^ (3 / 10 : ℝ) = 4 by
        rw [← Real.rpow_mul (show (0 : ℝ) ≤ 4 by norm_num),
            show (10 / 3 : ℝ) * (3 / 10) = 1 by norm_num, Real.rpow_one]] at h
  have hhalf : x ^ (1 / 2 : ℝ) = x ^ (3 / 10 : ℝ) * x ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hmain : (4 : ℝ) * x ^ (1 / 5 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hx0.le _)
  linarith [hmain]

theorem psi_sub_theta_le_230 (ξ : ℝ) (hξ : 30000 ≤ ξ) :
    Chebyshev.psi ξ - Chebyshev.theta ξ ≤ 2.3 * Real.sqrt ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hCP := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi ξ
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
      show (3 : ℝ)⁻¹ = (1 / 3 : ℝ) by norm_num,
      show (5 : ℝ)⁻¹ = (1 / 5 : ℝ) by norm_num] at hCP
  have hb2 := Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real (ξ ^ (1 / 2 : ℝ))
    (Real.rpow_nonneg hξ0.le _)
  have hb3 := Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real (ξ ^ (1 / 3 : ℝ))
    (Real.rpow_nonneg hξ0.le _)
  have hb5 := Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real (ξ ^ (1 / 5 : ℝ))
    (Real.rpow_nonneg hξ0.le _)
  have h3 := rpow_third_le_quarter (le_trans (by norm_num : (4096 : ℝ) ≤ 30000) hξ)
  have h5 := rpow_fifth_le_quarter (le_trans (by norm_num : (128 : ℝ) ≤ 30000) hξ)
  have hhalf_nn : (0 : ℝ) ≤ ξ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hξ0.le _
  have hsum : ξ ^ (1 / 2 : ℝ) + ξ ^ (1 / 3 : ℝ) + ξ ^ (1 / 5 : ℝ)
      ≤ (3 / 2) * ξ ^ (1 / 2 : ℝ) := by linarith [h3, h5]
  have hlog3nn : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hnum : Real.log 3 * (ξ ^ (1 / 2 : ℝ) + ξ ^ (1 / 3 : ℝ) + ξ ^ (1 / 5 : ℝ))
      ≤ 2.3 * ξ ^ (1 / 2 : ℝ) := by
    calc Real.log 3 * (ξ ^ (1 / 2 : ℝ) + ξ ^ (1 / 3 : ℝ) + ξ ^ (1 / 5 : ℝ))
        ≤ Real.log 3 * ((3 / 2) * ξ ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hsum hlog3nn
      _ = (Real.log 3 * (3 / 2)) * ξ ^ (1 / 2 : ℝ) := by ring
      _ ≤ 2.3 * ξ ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hhalf_nn
          nlinarith [Real.log_three_lt_d9]
  calc Chebyshev.psi ξ - Chebyshev.theta ξ
      ≤ Chebyshev.psi (ξ ^ (1 / 2 : ℝ)) + Chebyshev.psi (ξ ^ (1 / 3 : ℝ))
          + Chebyshev.psi (ξ ^ (1 / 5 : ℝ)) := hCP
    _ ≤ Real.log 3 * ξ ^ (1 / 2 : ℝ) + Real.log 3 * ξ ^ (1 / 3 : ℝ)
          + Real.log 3 * ξ ^ (1 / 5 : ℝ) := by linarith [hb2, hb3, hb5]
    _ = Real.log 3 * (ξ ^ (1 / 2 : ℝ) + ξ ^ (1 / 3 : ℝ) + ξ ^ (1 / 5 : ℝ)) := by ring
    _ ≤ 2.3 * ξ ^ (1 / 2 : ℝ) := hnum
    _ = 2.3 * Real.sqrt ξ := by rw [Real.sqrt_eq_rpow]

end Work.RHContract.A.regionII
