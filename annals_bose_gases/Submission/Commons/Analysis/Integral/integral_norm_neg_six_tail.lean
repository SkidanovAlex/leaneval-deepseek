import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory Set
open scoped Real

/-- The tail integral of `‖x‖⁻⁶` over `ℝ³`: `∫_{‖x‖ > R} ‖x‖⁻⁶ = 4π/(3R³)` for `R > 0` (from `∫_R^∞ r^{-4} dr = 1/(3R³)`). -/
theorem integral_norm_neg_six_tail {R : ℝ} (hR : 0 < R) :
    (∫ x : EuclideanSpace ℝ (Fin 3) in {x | R < ‖x‖}, ((‖x‖ : ℝ)⁻¹) ^ 6)
      = 4 * Real.pi / (3 * R ^ 3) := by
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1)
      = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]
    ring
  have hms : MeasurableSet {x : EuclideanSpace ℝ (Fin 3) | R < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin 3),
      {x | R < ‖x‖}.indicator (fun x => ((‖x‖ : ℝ)⁻¹) ^ 6) x
        = (Ioi R).indicator (fun y : ℝ => (y⁻¹) ^ 6) ‖x‖ := by
    intro x
    by_cases hx : x ∈ {x : EuclideanSpace ℝ (Fin 3) | R < ‖x‖}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show ‖x‖ ∈ Ioi R from hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show ‖x‖ ∉ Ioi R from hx)]
  have hinner : (∫ y in Ioi (0 : ℝ), y ^ 2 • ((Ioi R).indicator (fun y : ℝ => (y⁻¹) ^ 6)) y)
      = 1 / (3 * R ^ 3) := by
    have hcongr : Set.EqOn
        (fun y : ℝ => y ^ 2 • ((Ioi R).indicator (fun y : ℝ => (y⁻¹) ^ 6)) y)
        ((Ioi R).indicator (fun y : ℝ => y ^ (-4 : ℝ))) (Ioi (0 : ℝ)) := by
      intro y hy
      change y ^ 2 • ((Ioi R).indicator (fun y : ℝ => (y⁻¹) ^ 6)) y
        = ((Ioi R).indicator (fun y : ℝ => y ^ (-4 : ℝ))) y
      rw [mem_Ioi] at hy
      by_cases hyR : R < y
      · have hyR' : y ∈ Ioi R := hyR
        rw [Set.indicator_of_mem hyR', Set.indicator_of_mem hyR']
        simp only [smul_eq_mul]
        have hy0 : (0 : ℝ) < y := hR.trans hyR
        rw [show y ^ 2 * (y⁻¹) ^ 6 = (y ^ 4)⁻¹ by field_simp,
            show y ^ (-4 : ℝ) = (y ^ 4)⁻¹ by
              rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le,
                Real.rpow_natCast]]
      · have hyR' : y ∉ Ioi R := hyR
        rw [Set.indicator_of_notMem hyR', Set.indicator_of_notMem hyR']
        simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    rw [setIntegral_indicator measurableSet_Ioi]
    rw [inter_eq_right.mpr (Ioi_subset_Ioi hR.le)]
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR]
    rw [show (-4 : ℝ) + 1 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hR.le,
      Real.rpow_natCast]
    rw [neg_div_neg_eq, div_eq_mul_inv, one_div, mul_inv_rev]
    ring
  rw [← integral_indicator hms]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        ((Ioi R).indicator (fun y : ℝ => (y⁻¹) ^ 6))]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp]
  rw [show (3 : ℕ) - 1 = 2 from by norm_num]
  rw [hvol, hinner]
  simp only [nsmul_eq_mul, smul_eq_mul]
  field_simp
  norm_num

end Commons.Analysis.Integral