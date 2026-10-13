import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- Radial power integral over the ball of radius `r` in `ℝ³`:
`∫_{‖z‖<r} ‖z‖^s dz = 4π r^{s+3} / (s+3)` for `s > -3`.
Proved from the general radial decomposition `MeasureTheory.integral_fun_norm_addHaar`
together with the volume `|B_1| = 4π/3` and `∫_0^r y^{s+2} dy = r^{s+3}/(s+3)`. -/
theorem radial_rpow_integral (s : ℝ) (hs : -3 < s) (r : ℝ) (hr : 0 < r) :
    ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s
      = 4 * Real.pi * r ^ (s + 3) / (s + 3) := by
  have hfin : Module.finrank ℝ Work.LWP.R3 = 3 := by simp [finrank_euclideanSpace]
  -- rewrite the ball integral as the full-space integral of the radial profile
  -- `(Iio r).indicator (·^s)`
  have hball : ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s
      = ∫ z : Work.LWP.R3, ((Iio r).indicator (fun y : ℝ => y ^ s)) ‖z‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Metric.ball (0 : Work.LWP.R3) r
    · have hzr : ‖z‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show ‖z‖ ∈ Iio r from hzr)]
    · have hzr : ¬ ‖z‖ < r := by
        intro h; exact hz (by rwa [Metric.mem_ball, dist_zero_right])
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show ‖z‖ ∉ Iio r from hzr)]
  -- volume of the unit ball
  have hvol : volume.real (Metric.ball (0 : Work.LWP.R3) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    rw [show ENNReal.ofReal (1:ℝ) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
          = ENNReal.ofReal (Real.pi * 4 / 3) by simp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  -- the radial integral `∫_{Ioi 0} y^2 • indicator (Iio r) y^s = ∫_0^r y^{s+2} = r^{s+3}/(s+3)`
  have hInt : ∫ y in Ioi (0:ℝ), y ^ ((3:ℕ) - 1) • ((Iio r).indicator (fun y : ℝ => y ^ s)) y
      = r ^ (s + 3) / (s + 3) := by
    simp only [Nat.reduceSub]
    have hstep : ∫ y in Ioi (0:ℝ), y ^ (2:ℕ) • ((Iio r).indicator (fun y : ℝ => y ^ s)) y
        = ∫ y in Ioo (0:ℝ) r, y ^ (s + 2) := by
      rw [← integral_indicator measurableSet_Ioi]
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hy]
        by_cases hyr : y < r
        · rw [Set.indicator_of_mem (show y ∈ Iio r from hyr),
            Set.indicator_of_mem (show y ∈ Ioo (0:ℝ) r from ⟨hy, hyr⟩)]
          rw [smul_eq_mul, ← Real.rpow_natCast y 2, ← Real.rpow_add hy ((2:ℕ):ℝ) s,
            show ((2:ℕ):ℝ) + s = s + 2 by ring]
        · rw [Set.indicator_of_notMem (show y ∉ Iio r from hyr),
            Set.indicator_of_notMem (show y ∉ Ioo (0:ℝ) r from fun h => hyr h.2), smul_zero]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (show y ∉ Ioo (0:ℝ) r from fun h => hy (Ioo_subset_Ioi_self h))]
    rw [hstep]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < s + 2))]
    rw [show s + 2 + 1 = s + 3 by ring, Real.zero_rpow (by linarith : s + 3 ≠ 0)]
    rw [sub_zero]
  rw [hball, integral_fun_norm_addHaar volume ((Iio r).indicator (fun y : ℝ => y ^ s))]
  rw [hfin]
  rw [hInt, hvol]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end Work.CoreResiduals.BiotSavart
