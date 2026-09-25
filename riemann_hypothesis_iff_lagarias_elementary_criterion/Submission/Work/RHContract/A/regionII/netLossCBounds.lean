import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

namespace Work.RHContract.A.regionII

set_option linter.unusedVariables false

theorem netLossCBounds (ε : ℝ) (hε : 0 < ε) (hlo : (100000 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) :
    (9015 : ℝ) / 10000 / (Real.log (Work.RHPlan.caXi ε : ℝ) + 941 / 10000)
        ≤ Work.RHContract.Margin.caC ε * (Work.RHPlan.caXi ε : ℝ) ∧
      Work.RHContract.Margin.caC ε * (Work.RHPlan.caXi ε : ℝ)
        ≤ 1 / ((9 / 10 : ℝ) * (Real.log (Work.RHPlan.caXi ε : ℝ) - 105361 / 1000000)) := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  set L : ℝ := Real.log ξ with hLdef
  have hξ100000 : (100000 : ℝ) ≤ ξ := by rw [hξdef]; exact hlo
  have hξ0 : 0 < ξ := by linarith
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    refine le_trans ?_ (Real.log_le_log (by norm_num) hξ100000)
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 < L := by linarith
  -- the numerical input `3/√ξ ≤ 3/316.2`, i.e. `√ξ ≥ 316.2`
  have h3sqrt : 3 / Real.sqrt ξ ≤ 3 / (316.2 : ℝ) := by
    have h1 : Real.sqrt 100000 ≤ Real.sqrt ξ := Real.sqrt_le_sqrt hξ100000
    have h2 : 3 / Real.sqrt ξ ≤ 3 / Real.sqrt 100000 :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by norm_num)) h1
    have h3 : (316.2 : ℝ) ≤ Real.sqrt 100000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h4 : 3 / Real.sqrt 100000 ≤ 3 / (316.2 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
    linarith
  have hnum_ge : (9015 : ℝ) / 10000 * Real.log 3 ≤ 1 - 3 / Real.sqrt ξ := by
    linarith [Real.log_three_lt_d9, h3sqrt]
  -- Chebyshev bounds for `ψ ξ`
  have hpsi_ge9 : (9 / 10 : ℝ) * ξ ≤ Chebyshev.psi ξ :=
    le_trans (Commons.NumberTheory.Chebyshev.theta_lower_ninetenths ξ (by linarith))
      (Chebyshev.theta_le_psi ξ)
  have hψle : Chebyshev.psi ξ ≤ Real.log 3 * ξ :=
    Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real ξ hξ0.le
  have hψpos : 0 < Chebyshev.psi ξ := by linarith
  have hlogψpos : 0 < Real.log (Chebyshev.psi ξ) := Real.log_pos (by linarith)
  have hlogψle : Real.log (Chebyshev.psi ξ) ≤ L + 941 / 10000 := by
    have h1 : Real.log (Chebyshev.psi ξ) ≤ Real.log (Real.log 3 * ξ) :=
      Real.log_le_log hψpos hψle
    have h2 : Real.log (Real.log 3 * ξ) = Real.log (Real.log 3) + L := by
      rw [Real.log_mul hlog3pos.ne' hξ0.ne', hLdef]
    have h3 : Real.log (Real.log 3) ≤ 941 / 10000 := net_log_log3_le
    linarith
  have hdenpos : 0 < Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) := mul_pos hψpos hlogψpos
  have hL0941pos : 0 < L + 941 / 10000 := by linarith
  have hcaC : Work.RHContract.Margin.caC ε * ξ
      = ξ * (1 - 3 / Real.sqrt ξ) / (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by
    unfold Work.RHContract.Margin.caC
    rw [← hξdef]
    ring
  have hdenle : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)
      ≤ (Real.log 3 * ξ) * (L + 941 / 10000) :=
    mul_le_mul hψle hlogψle hlogψpos.le (by positivity)
  constructor
  · -- lower bound: `ψ ξ ≤ log 3 · ξ` and `log ψ ξ ≤ log(log 3) + L ≤ L + 0.0941`
    rw [hcaC, div_le_div_iff₀ hL0941pos hdenpos]
    have step1 : (9015 : ℝ) / 10000 * (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ))
        ≤ (9015 : ℝ) / 10000 * ((Real.log 3 * ξ) * (L + 941 / 10000)) :=
      mul_le_mul_of_nonneg_left hdenle (by norm_num)
    have step2 : (9015 : ℝ) / 10000 * ((Real.log 3 * ξ) * (L + 941 / 10000))
        ≤ (1 - 3 / Real.sqrt ξ) * (ξ * (L + 941 / 10000)) := by
      calc (9015 : ℝ) / 10000 * ((Real.log 3 * ξ) * (L + 941 / 10000))
          = ((9015 : ℝ) / 10000 * Real.log 3) * (ξ * (L + 941 / 10000)) := by ring
        _ ≤ (1 - 3 / Real.sqrt ξ) * (ξ * (L + 941 / 10000)) :=
            mul_le_mul_of_nonneg_right hnum_ge (mul_nonneg hξ0.le hL0941pos.le)
    calc (9015 : ℝ) / 10000 * (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ))
        ≤ (9015 : ℝ) / 10000 * ((Real.log 3 * ξ) * (L + 941 / 10000)) := step1
      _ ≤ (1 - 3 / Real.sqrt ξ) * (ξ * (L + 941 / 10000)) := step2
      _ = ξ * (1 - 3 / Real.sqrt ξ) * (L + 941 / 10000) := by ring
  · -- upper bound: `θ ξ ≥ 0.9 ξ`, hence `ψ ξ ≥ 0.9 ξ` and `log ψ ξ ≥ log 0.9 + L`
    rw [hcaC]
    have hthree_nonneg : (0 : ℝ) ≤ 3 / Real.sqrt ξ := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hstep1 : ξ * (1 - 3 / Real.sqrt ξ) / (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ))
        ≤ ξ / (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by
      apply div_le_div_of_nonneg_right _ hdenpos.le
      nlinarith [hξ0, hthree_nonneg]
    refine le_trans hstep1 ?_
    have hL'pos : 0 < (9 / 10 : ℝ) * (L - 105361 / 1000000) := by
      apply mul_pos (by norm_num); linarith
    rw [div_le_div_iff₀ hdenpos hL'pos]
    have hlog910 : -(105361 / 1000000 : ℝ) ≤ Real.log (9 / 10 : ℝ) := by
      have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (10 : ℝ) ≠ 0), h9]
      linarith [net_log_10_9_le]
    have hlogpsi_ge : L + Real.log (9 / 10 : ℝ) ≤ Real.log (Chebyshev.psi ξ) := by
      have h1 : Real.log ((9 / 10 : ℝ) * ξ) ≤ Real.log (Chebyshev.psi ξ) :=
        Real.log_le_log (mul_pos (by norm_num) hξ0) hpsi_ge9
      have h2 : Real.log ((9 / 10 : ℝ) * ξ) = Real.log (9 / 10) + L := by
        rw [Real.log_mul (by norm_num : (9 / 10 : ℝ) ≠ 0) hξ0.ne', hLdef]
      linarith
    have hB : L - 105361 / 1000000 ≤ Real.log (Chebyshev.psi ξ) := by linarith
    have hmul : ((9 / 10 : ℝ) * ξ) * (L - 105361 / 1000000)
        ≤ Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) :=
      mul_le_mul hpsi_ge9 hB (by linarith) hψpos.le
    calc ξ * ((9 / 10 : ℝ) * (L - 105361 / 1000000))
        = ((9 / 10 : ℝ) * ξ) * (L - 105361 / 1000000) := by ring
      _ ≤ Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) := hmul
      _ = 1 * (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by ring

end Work.RHContract.A.regionII

