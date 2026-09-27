import Mathlib
import Submission.Work.Mostow.gapA.slabDefs
import Submission.Work.Mostow.radialBallPolar
import Submission.Work.Mostow.gapA.radialClosedBallPolar
import Submission.Work.Mostow.gapA.lintegralCoshSinhc

/-!
# Tube measure of a ball in the normal 2-plane (`k = 1`, `m = 2`)

`Submission.Mostow.tubeMeasure k m` is the normal-fibre measure used in the Fermi-coordinate
decomposition of hyperbolic volume: it is Lebesgue measure on `E m` with density
`cosh ‖w‖^k * sinhc ‖w‖^(m−1)`.

For the case `k = 1`, `m = 2` the density is `cosh ‖w‖ * sinhc ‖w‖ = cosh ‖w‖ * sinh ‖w‖ / ‖w‖`,
so in polar coordinates on the plane the amount of tube measure carried by the closed ball of
radius `R ≥ 0` is

`∫_{‖w‖ ≤ R} cosh ‖w‖ sinhc ‖w‖ dw = 2π ∫₀^R cosh r sinh r dr = π sinh² R`,

using `∫₀^R cosh r sinh r dr = sinh²R / 2`.

This is the precise form (with the boundary sphere included) needed by the gap-A tube-volume
arguments, where the tube is a closed ball.
-/

open MeasureTheory MeasureTheory.Measure

open scoped ENNReal

namespace Work.Mostow.gapA

/-- The total surface measure of the unit circle in the plane: `(volume).toSphere univ = 2π`. -/
theorem toSphere_univ_fin_two :
    ((volume : Measure (EuclideanSpace ℝ (Fin 2))).toSphere Set.univ)
      = ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
    EuclideanSpace.volume_ball_fin_two]
  norm_num [ENNReal.ofReal_mul]

/-- `sinhc` is measurable (it is `x ↦ sinh x / x` off the origin). -/
theorem measurable_sinhc : Measurable Submission.Mostow.sinhc := by
  rw [show Submission.Mostow.sinhc
        = fun s : ℝ => if s = 0 then (1 : ℝ) else Real.sinh s / s from rfl]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Real.continuous_sinh.measurable.div measurable_id)

/-- The Lebesgue integral of the `(1,2)` normal-fibre density over the closed ball of radius
`R ≥ 0` is `π sinh² R`. -/
theorem tubeMeasure12Ball (R : ℝ) (hR : 0 ≤ R) :
    Submission.Mostow.tubeMeasure 1 2 (Metric.closedBall (0 : Submission.Mostow.E 2) R)
      = ENNReal.ofReal (Real.pi * Real.sinh R ^ 2) := by
  have hG : Measurable
      (fun x : ℝ => ENNReal.ofReal (Real.cosh x * Submission.Mostow.sinhc x)) :=
    (Real.continuous_cosh.measurable.mul measurable_sinhc).ennreal_ofReal
  have h21 : (2 : ℕ) - 1 = 1 := by norm_num
  -- unfold the density and evaluate the closed-ball integral in polar coordinates
  rw [Submission.Mostow.tubeMeasure, withDensity_apply _ measurableSet_closedBall]
  simp only [h21, pow_one]
  rw [radialClosedBallPolar (m := 2) (by norm_num) R hR _ hG]
  simp only [h21, pow_one]
  -- replace `sinhc` by `sinh x / x` on `Ioo 0 R` and evaluate the radial integral
  have hsinhc_eq : ∫⁻ x in Set.Ioo (0 : ℝ) R,
        ENNReal.ofReal x * ENNReal.ofReal (Real.cosh x * Submission.Mostow.sinhc x)
      = ENNReal.ofReal (Real.sinh R ^ 2 / 2) := by
    rw [← lintegralCoshSinhc R hR]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    obtain ⟨hx0, _⟩ := hx
    simp [Submission.Mostow.sinhc, ne_of_gt hx0]
  rw [toSphere_univ_fin_two, hsinhc_eq]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  congr 1
  ring

end Work.Mostow.gapA
