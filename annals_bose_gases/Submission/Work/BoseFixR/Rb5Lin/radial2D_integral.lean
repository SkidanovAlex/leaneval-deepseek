import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.radial2D_integral` — polar coordinates in the plane

For an arbitrary (not necessarily integrable) `Φ : ℝ → ℝ`,

    ∫_{ℝ²} Φ ‖y‖ dy = 2π ∫_{u>0} u * Φ u du.

This is the two-dimensional instance of Mathlib's general polar-coordinate identity for
additive Haar measures, `MeasureTheory.integral_fun_norm_addHaar`:

    ∫ x, f ‖x‖ ∂μ = (finrank ℝ E) • μ.real (ball 0 1) • ∫ y in Ioi 0, y ^ (finrank - 1) • f y

specialised to `E = EuclideanSpace ℝ (Fin 2)`, where `finrank ℝ E = 2` and the unit ball
has `real` measure `π` (`EuclideanSpace.volume_ball_fin_two`).  No integrability
hypothesis is required: the identity is between Bochner integrals (both sides vanish when
the function is not integrable), which is precisely the form used by the consumers.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixR.Rb5Lin

theorem radial2D_integral (Φ : ℝ → ℝ) :
    (∫ y : EuclideanSpace ℝ (Fin 2), Φ ‖y‖) = 2 * Real.pi * ∫ u in Set.Ioi (0 : ℝ), u * Φ u := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))).real
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = Real.pi := by
    rw [MeasureTheory.Measure.real_def, EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
      ENNReal.toReal_ofReal (le_of_lt Real.pi_pos)]
    norm_num
  rw [MeasureTheory.integral_fun_norm_addHaar
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)))) (f := Φ)]
  rw [hrank, show (2 : ℕ) - 1 = 1 from by norm_num, hvol]
  simp only [nsmul_eq_mul, smul_eq_mul, pow_one]
  ring

end Work.BoseFixR.Rb5Lin
