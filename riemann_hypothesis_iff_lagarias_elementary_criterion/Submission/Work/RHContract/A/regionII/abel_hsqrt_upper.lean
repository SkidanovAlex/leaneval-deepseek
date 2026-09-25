import Mathlib

open MeasureTheory intervalIntegral

namespace Work.RHContract.A.regionII

theorem abel_hsqrt_upper {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (2 * Real.log t + 1)/(t^3 * (Real.log t)^2) * Real.sqrt t
      ≤ ((2 + 1/Real.log a)/Real.log a) * (2/3)
          * (1/(a * Real.sqrt a) - 1/(b * Real.sqrt b)) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha
  have hCeq : (2 * Real.log a + 1) / (Real.log a)^2 = (2 + 1/Real.log a)/Real.log a := by
    have h : Real.log a ≠ 0 := ne_of_gt hla
    field_simp
  have hpow_a : a ^ (-(3:ℝ)/2) = 1/(a * Real.sqrt a) := by
    rw [Real.sqrt_eq_rpow]
    rw [show -(3:ℝ)/2 = -(1 + 1/2 : ℝ) by norm_num]
    rw [Real.rpow_neg ha0.le]
    rw [Real.rpow_add ha0]
    rw [Real.rpow_one]
    ring_nf
  have hpow_b : b ^ (-(3:ℝ)/2) = 1/(b * Real.sqrt b) := by
    have hb0 : (0:ℝ) < b := by linarith
    rw [Real.sqrt_eq_rpow]
    rw [show -(3:ℝ)/2 = -(1 + 1/2 : ℝ) by norm_num]
    rw [Real.rpow_neg hb0.le]
    rw [Real.rpow_add hb0]
    rw [Real.rpow_one]
    ring_nf
  have hint_rpow : ∫ x in a..b, x^(-(5:ℝ)/2) = (2/3)*(a^(-(3:ℝ)/2) - b^(-(3:ℝ)/2)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · rw [show (-(5:ℝ)/2 + 1) = -(3:ℝ)/2 by norm_num]
      ring
    · rw [Set.uIcc_of_le hab]
      intro h
      simp only [Set.mem_Icc] at h
      linarith [h.1, ha0]
  have hlic : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc a b) :=
    Real.continuousOn_log.mono (by
      intro x hx
      rw [Set.mem_Icc] at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (by linarith [hx.1, ha0]))
  have hpoint : ∀ t ∈ Set.Icc a b,
      (2 * Real.log t + 1)/(t^3 * (Real.log t)^2) * Real.sqrt t
        ≤ ((2*Real.log a+1)/(Real.log a)^2) * t^(-(5:ℝ)/2) := by
    intro t ht
    have hat : a ≤ t := ht.1
    have ht1 : 1 < t := lt_of_lt_of_le ha hat
    have ht0 : (0:ℝ) < t := by linarith
    have hLt : 0 < Real.log t := Real.log_pos ht1
    have hLaL : Real.log a ≤ Real.log t := Real.log_le_log ha0 hat
    have hphi : (2*Real.log t+1)/(Real.log t)^2 ≤ (2*Real.log a+1)/(Real.log a)^2 := by
      rw [div_le_div_iff₀ (pow_pos hLt 2) (pow_pos hla 2)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hLaL)
        (by positivity : (0:ℝ) ≤ 2*Real.log t*Real.log a + Real.log t + Real.log a)]
    have hsqrt : Real.sqrt t / t^3 = t^(-(5:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow]; rw [← Real.rpow_natCast]; rw [← Real.rpow_sub ht0]; norm_num
    have hg : (2 * Real.log t + 1)/(t^3 * (Real.log t)^2) * Real.sqrt t
        = ((2*Real.log t+1)/(Real.log t)^2) * t^(-(5:ℝ)/2) := by
      rw [← hsqrt]
      field_simp
    rw [hg]
    exact mul_le_mul_of_nonneg_right hphi (Real.rpow_nonneg ht0.le _)
  have hgi : IntervalIntegrable
      (fun t => (2 * Real.log t + 1)/(t^3 * (Real.log t)^2) * Real.sqrt t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul
    · apply ContinuousOn.div
      · exact (continuousOn_const.mul hlic).add continuousOn_const
      · exact (continuousOn_id.pow 3).mul (hlic.pow 2)
      · intro x hx
        rw [Set.mem_Icc] at hx
        have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
        have hx0 : 0 < x := by linarith
        have hlx : 0 < Real.log x := Real.log_pos hx1
        exact mul_ne_zero (pow_ne_zero 3 (ne_of_gt hx0)) (pow_ne_zero 2 (ne_of_gt hlx))
    · exact Real.continuous_sqrt.continuousOn
  have hui : IntervalIntegrable
      (fun t => ((2*Real.log a+1)/(Real.log a)^2) * t^(-(5:ℝ)/2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    rw [Set.mem_Icc] at hx
    have hx0 : 0 < x := by linarith [hx.1, ha0]
    exact ne_of_gt hx0
  calc
    ∫ t in a..b, (2 * Real.log t + 1)/(t^3 * (Real.log t)^2) * Real.sqrt t
        ≤ ∫ t in a..b, ((2*Real.log a+1)/(Real.log a)^2) * t^(-(5:ℝ)/2) :=
          integral_mono_on hab hgi hui hpoint
    _ = ((2*Real.log a+1)/(Real.log a)^2) * ∫ t in a..b, t^(-(5:ℝ)/2) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ((2*Real.log a+1)/(Real.log a)^2) * ((2/3)*(a^(-(3:ℝ)/2) - b^(-(3:ℝ)/2))) := by
          rw [hint_rpow]
    _ = ((2 + 1/Real.log a)/Real.log a) * (2/3) * (1/(a * Real.sqrt a) - 1/(b * Real.sqrt b)) := by
          rw [hpow_a, hpow_b, hCeq]
          ring

end Work.RHContract.A.regionII
