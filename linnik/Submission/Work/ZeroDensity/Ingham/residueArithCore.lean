import Mathlib
import Submission.Work.ZeroDensity.Ingham.residueCommonsDeps

namespace Work.ZeroDensity.Ingham

/-- Constant part of the estimate: the explicit Gamma constant `K11` combined with the
polynomial factor `2^20` is completely absorbed by the exponential factor `exp(-45000 π)`. -/
private lemma K11ExpNegBoundAux :
    Commons.Analysis.Complex.K11 * 2 ^ 20 * Real.exp (-45000 * Real.pi) ≤ 1 / 20 := by
  have hK : Commons.Analysis.Complex.K11
      = (10:ℝ)^11 * Real.exp 1 * (Real.pi/2)^(11:ℝ) := by
    unfold Commons.Analysis.Complex.K11 Commons.Analysis.Complex.Mbig; ring
  have hpi2 : (Real.pi/2)^(11:ℝ) ≤ (2:ℝ)^11 := by
    have h : (Real.pi/2)^(11:ℝ) ≤ (2:ℝ)^(11:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith [Real.pi_lt_four]) (by norm_num)
    rwa [show (2:ℝ)^(11:ℝ) = (2:ℝ)^11 by norm_num] at h
  have hKle : Commons.Analysis.Complex.K11 ≤ (10:ℝ)^11 * 3 * 2^11 := by
    rw [hK]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (by positivity)
    · exact hpi2
    · positivity
    · positivity
  have step1 : 20 * (Commons.Analysis.Complex.K11 * 2^20)
      ≤ 20 * ((10:ℝ)^11 * 3 * 2^11 * 2^20) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_right hKle (by positivity)
  have step2 : 20 * ((10:ℝ)^11 * 3 * 2^11 * 2^20) = 60 * (10:ℝ)^11 * 2^31 := by ring
  have step3 : 60 * (10:ℝ)^11 * 2^31 ≤ (2:ℝ)^100 := by norm_num
  have step4 : (2:ℝ)^100 ≤ (2:ℝ)^135000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have step5 : (2:ℝ)^135000 ≤ Real.exp (135000 : ℝ) := by
    rw [show (135000:ℝ) = (135000:ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 135000
  have step6 : Real.exp (135000 : ℝ) ≤ Real.exp (45000 * Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_gt_three]
  have hkey : 20 * (Commons.Analysis.Complex.K11 * 2^20) ≤ Real.exp (45000 * Real.pi) :=
    le_trans step1 (le_trans step2.le (le_trans step3 (le_trans step4 (le_trans step5 step6))))
  have hpos : (0:ℝ) < Real.exp (45000 * Real.pi) := Real.exp_pos _
  rw [show -45000 * Real.pi = -(45000 * Real.pi) by ring, Real.exp_neg]
  rw [mul_inv_le_iff₀ hpos]
  calc Commons.Analysis.Complex.K11 * 2^20
      = (1/20) * (20 * (Commons.Analysis.Complex.K11 * 2^20)) := by ring
    _ ≤ (1/20) * Real.exp (45000 * Real.pi) := mul_le_mul_of_nonneg_left hkey (by norm_num)

lemma residueArithCore (A T : ℝ) (hA : Real.exp 300 ≤ A) (hT : 2 ≤ T) :
    Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2)
      * (1 + T) ^ 20 * T * (1 + Real.log T) ≤ 1 / 20 := by
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos 300) hA
  have hTpos : 0 < T := by linarith
  have ht_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hAT : Real.log (A * T) = Real.log A + Real.log T :=
    Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)
  have hlogA : 300 ≤ Real.log A := by
    have h := Real.log_le_log (Real.exp_pos 300) hA
    rwa [Real.log_exp] at h
  have hge : 300 + Real.log T ≤ Real.log (A * T) := by rw [hAT]; linarith
  have hnonneg : 0 ≤ 300 + Real.log T := by linarith
  have hsq : (300 + Real.log T)^2 ≤ (Real.log (A*T))^2 := by
    nlinarith [hge, hnonneg, sq_nonneg (Real.log (A*T)), sq_nonneg (300 + Real.log T)]
  have hKpos : 0 < Commons.Analysis.Complex.K11 := Commons.Analysis.Complex.K11_pos
  have hexp : Real.exp (-(Real.pi/2) * (Real.log (A*T))^2)
      ≤ Real.exp (-(Real.pi/2) * (300 + Real.log T)^2) := by
    apply Real.exp_le_exp.mpr
    have hp : (0:ℝ) < Real.pi/2 := by positivity
    nlinarith [hsq]
  have hpoly : (1 + T)^20 * T * (1 + Real.log T)
      ≤ 2^20 * Real.exp (22 * Real.log T) := by
    have h3 : 1 + Real.log T ≤ T := by
      have h := Real.add_one_le_exp (Real.log T)
      rw [Real.exp_log hTpos] at h
      linarith
    have h1 : (1 + T)^20 ≤ 2^20 * T^20 := by
      have h2T : (1 + T)^20 ≤ (2 * T)^20 := pow_le_pow_left₀ (by linarith) (by linarith) 20
      rwa [mul_pow] at h2T
    have h22 : Real.exp (22 * Real.log T) = T^22 := by
      have hcast : ((22:ℕ):ℝ) = (22:ℝ) := by norm_num
      rw [← hcast, Real.exp_nat_mul, Real.exp_log hTpos]
    calc (1 + T)^20 * T * (1 + Real.log T)
        ≤ (2^20 * T^20) * T * T := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hTpos.le) h3
          · linarith
          · positivity
      _ = 2^20 * Real.exp (22 * Real.log T) := by rw [h22]; ring
  have hPnonneg : 0 ≤ (1 + T)^20 * T * (1 + Real.log T) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) 20) hTpos.le) (by linarith)
  calc
    Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * (Real.log (A * T)) ^ 2)
      * (1 + T) ^ 20 * T * (1 + Real.log T)
        = (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi/2) * (Real.log (A*T))^2))
            * ((1 + T)^20 * T * (1 + Real.log T)) := by ring
      _ ≤ (Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi/2) * (300 + Real.log T)^2))
            * (2^20 * Real.exp (22 * Real.log T)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hexp hKpos.le
          · exact hpoly
          · exact hPnonneg
          · exact mul_nonneg hKpos.le (Real.exp_pos _).le
      _ = Commons.Analysis.Complex.K11 * 2^20
            * Real.exp (-(Real.pi/2) * (300 + Real.log T)^2 + 22 * Real.log T) := by
          rw [Real.exp_add]; ring
      _ ≤ Commons.Analysis.Complex.K11 * 2^20 * Real.exp (-45000 * Real.pi) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hKpos.le (by positivity))
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_gt_three, ht_nonneg, sq_nonneg (Real.log T)]
      _ ≤ 1 / 20 := K11ExpNegBoundAux

end Work.ZeroDensity.Ingham
