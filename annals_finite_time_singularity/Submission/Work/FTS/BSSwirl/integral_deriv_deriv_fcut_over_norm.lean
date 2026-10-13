/-
# The `-4π` normalisation of the cutoff `fcut` on `ℝ³`

This module proves

  `∫_{ℝ³} (deriv (deriv fcut)) ‖w‖ / ‖w‖ dw = -4π`,

the scalar identity behind the `-Δ(1/‖·‖) = 4π δ` normalisation used by the
Newtonian-potential chapter of `Work.FTS.BSSwirl` (compare
`integral_inv_norm_mul_laplacian`).

Writing `F := deriv (deriv fcut)`, the integrand `x ↦ F ‖x‖ / ‖x‖` is radial, so the
polar-coordinate formula `MeasureTheory.integral_fun_norm_addHaar` for `ℝ³` gives

  `∫_{ℝ³} F ‖x‖ / ‖x‖ dx = 3 • volume.real (ball 0 1) • ∫_0^∞ y^{3-1} • F y / y dy
                         = 4π ∫_0^∞ y * F y dy`

(`volume.real (ball 0 1) = 4π/3`, and `y^2 * (F y / y) = y * F y` for every `y`), and the
remaining one-dimensional integral is evaluated in the companion module
`Work.FTS.BSSwirl.integral_Ioi_mul_deriv_deriv_fcut`:

  `∫_0^∞ y * fcut''(y) dy = -1`

(`fcut''` is supported in `[1,2]`, and `y ↦ y * fcut'(y) - fcut(y)` is an antiderivative
whose increment is `(2·0 - 1) - (1·0 - 0) = -1`).  Hence the total is `4π * (-1) = -4π`.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.FTS.BSSwirl.inv_norm_cut
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.integral_Ioi_mul_deriv_deriv_fcut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.BSSwirl

noncomputable section

/-- **Polar-coordinate reduction of a radial integral on `ℝ³`.**  For any `F : ℝ → ℝ`,

  `∫_{ℝ³} F ‖x‖ / ‖x‖ dx = 4π ∫_0^∞ y * F y dy`,

because `MeasureTheory.integral_fun_norm_addHaar` turns the left-hand side into
`3 • volume.real (ball 0 1) • ∫_0^∞ y^{3-1} • F y / y dy`, and then
`volume.real (ball 0 1) = 4π/3` while `y^2 * (F y / y) = y * F y` pointwise (the latter
identity includes `y = 0`, where both sides vanish). -/
private lemma integral_norm_radial_div (F : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), F ‖x‖ / ‖x‖ = 4 * Real.pi * ∫ y in Set.Ioi (0 : ℝ), y * F y := by
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun y : ℝ => F y / y)]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp [finrank_euclideanSpace]
  rw [hfin]
  norm_num
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1)
      = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    rw [show ENNReal.ofReal (1 : ℝ) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
        = ENNReal.ofReal (Real.pi * 4 / 3) by simp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hvol]
  have hcongr : (∫ y in Set.Ioi (0 : ℝ), y ^ 2 * (F y / y))
      = ∫ y in Set.Ioi (0 : ℝ), y * F y := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy' : y ≠ 0 := ne_of_gt hy
    field_simp
  rw [hcongr]
  ring

/-- The `F = fcut''` case of `integral_norm_radial_div`. -/
private lemma integral_norm_radial_fcut_deriv2 :
    ∫ x : EuclideanSpace ℝ (Fin 3), deriv (deriv fcut) ‖x‖ / ‖x‖
      = 4 * Real.pi * ∫ y in Set.Ioi (0 : ℝ), y * deriv (deriv fcut) y :=
  integral_norm_radial_div (fun y => deriv (deriv fcut) y)

/-- **The `-4π` normalisation of the smooth cutoff.**  The radial second derivative of the
smooth step `fcut`, weighted by `‖w‖⁻¹`, integrates over `ℝ³` to `-4π`, the fundamental
solution of the Laplacian. -/
theorem integral_deriv_deriv_fcut_over_norm :
    ∫ w : EuclideanSpace ℝ (Fin 3), deriv (deriv Work.FTS.BSSwirl.fcut) ‖w‖ / ‖w‖ = -4 * Real.pi := by
  rw [integral_norm_radial_fcut_deriv2, integral_Ioi_mul_deriv_deriv_fcut]
  ring

end

end Work.FTS.BSSwirl
