import Mathlib
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector
import Submission.Commons.MeasureTheory.Integral.ofReal_chord_sq_div_add_le_lintegral_deriv

namespace Commons.MeasureTheory.Integral

theorem ofReal_norm_smul_sub_le_lintegral_deriv_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b s t : ℝ} (hs : 0 < s) (ht : t ∈ Set.Ioc a (b - s))
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
      ≤ ENNReal.ofReal s⁻¹ * ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) := by
  obtain ⟨hat, htbs⟩ := ht
  have hab : a ≤ b := by linarith
  have hts_le : t + s ≤ b := by linarith
  have ht_le : t ≤ t + s := by linarith
  have hac : AbsolutelyContinuousOnInterval f t (t + s) := by
    refine hf.mono ?_
    rw [Set.uIcc_of_le ht_le, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc hat.le hts_le
  have hsq := ofReal_sq_norm_sub_le_lintegral_sq_deriv_mul (a := t) (b := t + s) ht_le hac
  rw [show t + s - t = s by ring] at hsq
  have hv : ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2
      = s⁻¹ * s⁻¹ * ‖f (t + s) - f t‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    ring
  have hpeq : ENNReal.ofReal (s⁻¹ * s⁻¹ * ‖f (t + s) - f t‖ ^ 2)
      = ENNReal.ofReal s⁻¹ * ENNReal.ofReal s⁻¹
        * ENNReal.ofReal (‖f (t + s) - f t‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hs.le) (inv_nonneg.mpr hs.le)),
      ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)]
  rw [hv, hpeq]
  have hp : ENNReal.ofReal s⁻¹ * ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hs.le), inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one]
  have hcollapse : ENNReal.ofReal s⁻¹ * ENNReal.ofReal s⁻¹
      * ((∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2)) * ENNReal.ofReal s)
      = ENNReal.ofReal s⁻¹
        * ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) := by
    have haux : ENNReal.ofReal s⁻¹
          * ((∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2)) * ENNReal.ofReal s)
        = ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) := by
      calc ENNReal.ofReal s⁻¹
            * ((∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2)) * ENNReal.ofReal s)
          = ENNReal.ofReal s⁻¹
              * (∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2))
              * ENNReal.ofReal s := by rw [mul_assoc]
        _ = (∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2))
              * ENNReal.ofReal s⁻¹ * ENNReal.ofReal s := by
              rw [mul_comm (ENNReal.ofReal s⁻¹)
                (∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2))]
        _ = (∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2))
              * (ENNReal.ofReal s⁻¹ * ENNReal.ofReal s) := by rw [mul_assoc]
        _ = (∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2)) * 1 := by rw [hp]
        _ = ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) := by rw [mul_one]
    rw [mul_assoc, haux]
  calc ENNReal.ofReal s⁻¹ * ENNReal.ofReal s⁻¹
        * ENNReal.ofReal (‖f (t + s) - f t‖ ^ 2)
      ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal s⁻¹
        * ((∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2))
            * ENNReal.ofReal s) := mul_le_mul_right hsq _
    _ = ENNReal.ofReal s⁻¹
        * ∫⁻ u in Set.Ioc t (t + s), ENNReal.ofReal (‖deriv f u‖ ^ 2) := hcollapse

end Commons.MeasureTheory.Integral
