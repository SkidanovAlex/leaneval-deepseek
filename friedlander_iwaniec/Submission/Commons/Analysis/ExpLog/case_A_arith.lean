import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

set_option autoImplicit false

namespace Commons.Analysis.ExpLog

theorem case_A_arith (c0 Kp : ℝ) (hc0 : 0 < c0) (hc0le : c0 ≤ 1) (hKp : 0 < Kp) :
    ∃ K Z0 : ℝ, 0 ≤ K ∧ 3 ≤ Z0 ∧ ∀ z w : ℝ, Z0 ≤ z → 3 ≤ w → z ^ 2 ≤ w →
      Real.log w / Real.log z ≤ Real.log z →
      Kp * (Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5
        + (Real.log z) ^ 3 * (Real.log (z ^ (c0 / 4) + 2) + 1) / z ^ (c0 / 4)
        + 3 * (Real.log w + 1) / z ^ (c0 / 4))
      ≤ K * (z ^ (-(c0 / 16)) + Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6) := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  have hc04 : 0 ≤ c0 / 4 := le_of_lt (div_pos hc0 (by norm_num))
  have h3c0 : 0 < 3 * c0 / 16 := div_pos (mul_pos (by norm_num) hc0) (by norm_num)
  obtain ⟨X, _hX1, hXbound⟩ :=
    const_mul_log_pow_le_rpow_threshold (K := Real.log 3 + 6) (by linarith)
      (n := 4) (r := 3 * c0 / 16) h3c0
  refine ⟨3 * Kp, max 3 (max (Real.exp 1) X), ?_, ?_, ?_⟩
  · linarith
  · exact le_max_left _ _
  · intro z w hz hw hw2 hcond
    have hz_exp : Real.exp 1 ≤ z :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hz)
    have hzX : X ≤ z := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hz)
    have hz0 : 0 < z := by
      have : (3:ℝ) ≤ z := le_trans (le_max_left _ _) hz
      linarith
    have hz1 : (1:ℝ) ≤ z := by linarith
    set L : ℝ := Real.log z with hL
    set M : ℝ := Real.log w with hM
    set Rbig : ℝ := z ^ (-(c0/16)) + Real.exp (-(M/L)) * L^6 with hRbig
    have hL1 : 1 ≤ L := by
      rw [hL]
      simpa using Real.log_le_log (Real.exp_pos 1) hz_exp
    have hL0 : 0 < L := by linarith
    have hLnn : 0 ≤ L := le_of_lt hL0
    have hM2 : M ≤ L^2 := by
      have := (div_le_iff₀ hL0).mp hcond
      rwa [pow_two]
    have hXz : (Real.log 3 + 6) * L^4 ≤ z ^ (3*c0/16) := by
      have := hXbound z hzX
      rwa [← hL] at this
    have hzrpow_pos : (0:ℝ) < z ^ (c0/4) := Real.rpow_pos_of_pos hz0 _
    -- logarithm bound
    have ha1 : (1:ℝ) ≤ z ^ (c0/4) := Real.one_le_rpow hz1 hc04
    have hapos : 0 < z^(c0/4) + 2 := by
      have := Real.rpow_pos_of_pos hz0 (c0/4); linarith
    have hlogb : Real.log (z^(c0/4)+2) ≤ Real.log 3 + (c0/4)*L := by
      have ha2 : z^(c0/4) + 2 ≤ 3 * z^(c0/4) := by nlinarith [ha1]
      have h1 : Real.log (z^(c0/4)+2) ≤ Real.log (3 * z^(c0/4)) :=
        Real.log_le_log hapos ha2
      have h2 : Real.log (3 * z^(c0/4)) = Real.log 3 + (c0/4)*L := by
        rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt hzrpow_pos)]
        rw [Real.log_rpow hz0 (c0/4), ← hL]
      rwa [h2] at h1
    -- main bound for A2
    have hmain2 : L^3 * (Real.log (z^(c0/4)+2) + 1) ≤ z^(3*c0/16) := by
      have hlog32 : Real.log 3 < 2 := by
        have := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 3 by norm_num) (by norm_num)
        linarith
      have hc4L : (c0/4)*L ≤ L := by
        have hc4 : c0/4 ≤ 1 := by linarith
        nlinarith [hLnn, hc4]
      have hstepA : Real.log (z^(c0/4)+2) + 1 ≤ 3 + L := by linarith [hlogb, hlog32, hc4L]
      have hstepB : L^3 * (Real.log (z^(c0/4)+2)+1) ≤ L^3 * (3 + L) :=
        mul_le_mul_of_nonneg_left hstepA (pow_nonneg hLnn 3)
      have hstepC : L^3 * (3 + L) ≤ 4 * L^4 := by
        have hL3le : L^3 ≤ L^4 := pow_le_pow_right₀ hL1 (by norm_num)
        nlinarith [hL3le]
      have h4D : (4:ℝ) * L^4 ≤ (Real.log 3 + 6) * L^4 :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLnn 4)
      exact le_trans hstepB (le_trans hstepC (le_trans h4D hXz))
    -- main bound for A3
    have hmain3 : 3*(M+1) ≤ z^(3*c0/16) := by
      have h1 : 3*(M+1) ≤ 3*(L^2+1) := by linarith [hM2]
      have h2 : 3*(L^2+1) ≤ 6*L^4 := by
        have hL2le : L^2 ≤ L^4 := pow_le_pow_right₀ hL1 (by norm_num)
        have h1le : (1:ℝ) ≤ L^4 := one_le_pow₀ hL1
        nlinarith [hL2le, h1le]
      have h3 : (6:ℝ)*L^4 ≤ (Real.log 3 + 6)*L^4 :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLnn 4)
      exact le_trans h1 (le_trans h2 (le_trans h3 hXz))
    have hexpnn : 0 ≤ Real.exp (-(M/L)) := (Real.exp_pos _).le
    have hzneg : 0 ≤ z ^ (-(c0/16)) := Real.rpow_nonneg hz0.le _
    have hterm6nn : 0 ≤ Real.exp (-(M/L)) * L^6 := mul_nonneg hexpnn (pow_nonneg hLnn 6)
    have hA1 : Real.exp (-(M/L)) * L^5 ≤ Rbig := by
      rw [hRbig]
      have hL5le : L^5 ≤ L^6 := pow_le_pow_right₀ hL1 (by norm_num)
      have h1 : Real.exp (-(M/L)) * L^5 ≤ Real.exp (-(M/L)) * L^6 :=
        mul_le_mul_of_nonneg_left hL5le hexpnn
      exact le_trans h1 (by linarith)
    have heq : z^(-(c0/16)) * z^(c0/4) = z^(3*c0/16) := by
      rw [← Real.rpow_add hz0]; congr 1; ring
    have hA2 : L^3 * (Real.log (z^(c0/4)+2)+1)/z^(c0/4) ≤ Rbig := by
      rw [hRbig]
      have hle : L^3*(Real.log (z^(c0/4)+2)+1)/z^(c0/4) ≤ z^(-(c0/16)) := by
        rw [div_le_iff₀ hzrpow_pos, heq]
        exact hmain2
      exact le_trans hle (by linarith)
    have hA3 : 3*(M+1)/z^(c0/4) ≤ Rbig := by
      rw [hRbig]
      have hle : 3*(M+1)/z^(c0/4) ≤ z^(-(c0/16)) := by
        rw [div_le_iff₀ hzrpow_pos, heq]
        exact hmain3
      exact le_trans hle (by linarith)
    have hsum : Real.exp (-(M/L))*L^5 + L^3*(Real.log (z^(c0/4)+2)+1)/z^(c0/4)
        + 3*(M+1)/z^(c0/4) ≤ 3*Rbig := by linarith [hA1, hA2, hA3]
    have hstep : Kp * (Real.exp (-(M/L))*L^5 + L^3*(Real.log (z^(c0/4)+2)+1)/z^(c0/4)
          + 3*(M+1)/z^(c0/4)) ≤ Kp * (3*Rbig) :=
      mul_le_mul_of_nonneg_left hsum hKp.le
    have hfinal : Kp * (3*Rbig) = (3*Kp) * Rbig := by ring
    rw [hfinal] at hstep
    exact hstep

end Commons.Analysis.ExpLog