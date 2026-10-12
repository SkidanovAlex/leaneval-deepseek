import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory Set
open scoped Real

/-- **Spherical coordinates in three dimensions, tail version**: integrating a radially symmetric integrand over the exterior `{x | R < ‖x‖}` of a ball of radius `R ≥ 0` reduces to `4π ∫_R^∞ y² F y dy`. -/
theorem radial_integral_three_Ioi (F : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : EuclideanSpace ℝ (Fin 3) in {x | R < ‖x‖}, F ‖x‖) =
      4 * Real.pi * ∫ y in Set.Ioi R, y ^ 2 * F y := by
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]
    ring
  set g : ℝ → ℝ := (Ioi R).indicator F with hg
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin 3),
      ({x : EuclideanSpace ℝ (Fin 3) | R < ‖x‖}).indicator (fun x => F ‖x‖) x = g ‖x‖ := by
    intro x
    rw [hg]
    by_cases hx : R < ‖x‖
    · rw [Set.indicator_of_mem (show x ∈ {y : EuclideanSpace ℝ (Fin 3) | R < ‖y‖} from hx),
        Set.indicator_of_mem (show ‖x‖ ∈ Ioi R from hx)]
    · rw [Set.indicator_of_notMem (show x ∉ {y : EuclideanSpace ℝ (Fin 3) | R < ‖y‖} from hx),
        Set.indicator_of_notMem (show ‖x‖ ∉ Ioi R from hx)]
  have hJ : (∫ y in Ioi (0:ℝ), y ^ 2 • g y) = ∫ y in Ioi R, y ^ 2 * F y := by
    have hcongr : Set.EqOn (fun y : ℝ => y ^ 2 • g y)
        (fun y : ℝ => (Ioi R).indicator (fun y => y ^ 2 * F y) y) (Ioi 0) := by
      intro y hy
      dsimp only
      rw [hg]
      by_cases hyR : y ∈ Ioi R
      · rw [Set.indicator_of_mem hyR, smul_eq_mul, Set.indicator_of_mem hyR]
      · rw [Set.indicator_of_notMem hyR, smul_eq_mul, mul_zero, Set.indicator_of_notMem hyR]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
        setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi hR)]
  have hL : (∫ x : EuclideanSpace ℝ (Fin 3) in {x | R < ‖x‖}, F ‖x‖)
      = ∫ x : EuclideanSpace ℝ (Fin 3), g ‖x‖ := by
    rw [← MeasureTheory.integral_indicator
      (s := {x : EuclideanSpace ℝ (Fin 3) | R < ‖x‖}) (by measurability)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [hL,
    MeasureTheory.integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (f := g)]
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp]
  rw [show (3:ℕ) - 1 = 2 from by norm_num]
  rw [hvol, hJ]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end Commons.Analysis.Integral