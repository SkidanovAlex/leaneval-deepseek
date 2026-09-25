import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.NN.Core.fiberPot_eq_shiftIntegral
import Submission.Work.CR.Flat.Cauchy

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory Set

namespace Work.NN.Core

/-- Replacing the `j`-th coordinate of `z` by `z j + w` is the same as adding `w e_j` to `z`. -/
lemma update_add_eq_add_update {n : ℕ} (z : Cn n) (j : Fin n) (w : ℂ) :
    Function.update z j (z j + w) = z + Function.update (0 : Cn n) j w := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp
  · simp [Function.update_of_ne hl]

/-- The shifted Cauchy integrand `s ↦ v (z + s e_j)/s` is integrable on a disc: the numerator is
continuous, hence bounded on the closed disc, and `‖s‖⁻¹` is integrable on a disc. -/
lemma integrableOn_slice_div {n : ℕ} (j : Fin n) {v : Cn n → ℂ} (hv : Continuous v)
    (z : Cn n) (ρ : ℝ) :
    IntegrableOn (fun w : ℂ => v (z + Function.update (0 : Cn n) j w) / w)
      (Metric.ball 0 ρ) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [Metric.ball_eq_empty.mpr hρ]
    exact integrableOn_empty
  have hcont : Continuous fun w : ℂ => v (z + Function.update (0 : Cn n) j w) :=
    hv.comp (continuous_const.add (continuous_update (0 : Cn n) j))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ((Work.CR.Flat.Cauchy.integrableOn_inv_ball ρ).norm.const_mul M).mono' ?_ ?_
  · exact (hcont.measurable.div measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
    have hb : ‖v (z + Function.update (0 : Cn n) j w)‖ ≤ M :=
      hM _ (Metric.ball_subset_closedBall hw)
    calc ‖v (z + Function.update (0 : Cn n) j w) / w‖
        = ‖v (z + Function.update (0 : Cn n) j w)‖ * ‖w⁻¹‖ := by
          rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ M * ‖w⁻¹‖ := mul_le_mul_of_nonneg_right hb (by positivity)

/-- The fixed-disc potential of band-supported data is the fibrewise Cauchy transform of the slice. For `‖z j‖ < R` one may translate the pole so that the fixed disc `‖w‖ < R` becomes the disc of radius `2R` centred at the origin (in the variable `s = w - z j`), and the data outside the band vanish, so that the two integrals agree:
`fiberPot R j v z = -(1/π) ∫_{‖w‖<R} v (z[j:=w])/(w - z j) dw = -(1/π) ∫_{‖s‖<2R} (v (z + s e_j) - v z)/s ds
= cauchyTransform (2R) (fiberSlice j v z) (z j)`.
Suggested route: `fiberPot_eq_shiftIntegral` (in `Submission/Work/NN/Core/fiberPot_eq_shiftIntegral.lean`) rewrites the left-hand side as an integral over `ball (-(z j)) R` of `s ↦ v (z + s e_j)/s`; the support hypothesis `hband` shows the integrand vanishes outside `ball 0 (2R)` (from `‖z j‖ < R`), and the subtracted term `v z · ∫_{‖s‖<2R} s⁻¹ = 0` is `Work.CR.Flat.integral_inv_ball`. -/
theorem fiberPot_eq_cauchyTransform {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) {v : Cn n → ℂ}
    (hv : ContDiff ℝ 0 v) (hband : fiberBand R j v) {z : Cn n} (hz : ‖z j‖ < R) :
    fiberPot R j v z = Work.CR.Flat.cauchyTransform (2 * R) (fiberSlice j v z) (z j) := by
  have hvcont : Continuous v := hv.continuous
  have hGint : IntegrableOn (fun w : ℂ => v (z + Function.update (0 : Cn n) j w) / w)
      (Metric.ball 0 (2 * R)) := integrableOn_slice_div j hvcont z (2 * R)
  have hczint : IntegrableOn (fun w : ℂ => v z / w) (Metric.ball 0 (2 * R)) := by
    have h : (fun w : ℂ => v z / w) = fun w : ℂ => v z * w⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [h]
    exact (Work.CR.Flat.Cauchy.integrableOn_inv_ball (2 * R)).const_mul (v z)
  have hcz0 : ∫ w in Metric.ball (0 : ℂ) (2 * R), v z / w = 0 := by
    have h : (fun w : ℂ => v z / w) = fun w : ℂ => v z * w⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [h, integral_const_mul, Work.CR.Flat.integral_inv_ball (2 * R), mul_zero]
  -- the translated disc sits inside the disc of radius `2R`
  have hsub : Metric.ball (-(z j)) R ⊆ Metric.ball (0 : ℂ) (2 * R) := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hs' : ‖s + z j‖ < R := by simpa [sub_eq_add_neg] using hs
    have h1 : ‖s‖ ≤ ‖s + z j‖ + ‖z j‖ := by
      have h := norm_add_le (s + z j) (-(z j))
      simpa [sub_eq_add_neg] using h
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  -- and the integrand vanishes off the translated disc
  have hsupp : ∫ w in Metric.ball (0 : ℂ) (2 * R),
        v (z + Function.update (0 : Cn n) j w) / w
      = ∫ s in Metric.ball (-(z j)) R, v (z + Function.update (0 : Cn n) j s) / s := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub ?_
    intro s hs
    rw [Set.mem_sdiff] at hs
    obtain ⟨-, hsnot⟩ := hs
    have hjb : R ≤ ‖(z + Function.update (0 : Cn n) j s) j‖ := by
      have hj : (z + Function.update (0 : Cn n) j s) j = z j + s := by
        simp
      rw [hj]
      refine not_lt.mp ?_
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm] using hsnot
    rw [hband _ hjb, zero_div]
  have hmain : ∫ s in Metric.ball (-(z j)) R, v (z + Function.update (0 : Cn n) j s) / s
      = ∫ w in Metric.ball (0 : ℂ) (2 * R),
          (fiberSlice j v z (z j + w) - fiberSlice j v z (z j)) / w := by
    have step1 : ∫ w in Metric.ball (0 : ℂ) (2 * R),
          (fiberSlice j v z (z j + w) - fiberSlice j v z (z j)) / w
        = ∫ w in Metric.ball (0 : ℂ) (2 * R),
          (v (z + Function.update (0 : Cn n) j w) / w - v z / w) := by
      refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
      have h1 : fiberSlice j v z (z j + w) = v (z + Function.update (0 : Cn n) j w) := by
        rw [fiberSlice_apply, update_add_eq_add_update z j w]
      have h2 : fiberSlice j v z (z j) = v z := by
        simp [fiberSlice]
      rw [h1, h2, sub_div]
    have step2 : ∫ w in Metric.ball (0 : ℂ) (2 * R),
          (v (z + Function.update (0 : Cn n) j w) / w - v z / w)
        = (∫ w in Metric.ball (0 : ℂ) (2 * R),
              v (z + Function.update (0 : Cn n) j w) / w)
          - ∫ w in Metric.ball (0 : ℂ) (2 * R), v z / w :=
      integral_sub hGint hczint
    calc ∫ s in Metric.ball (-(z j)) R, v (z + Function.update (0 : Cn n) j s) / s
        = ∫ w in Metric.ball (0 : ℂ) (2 * R),
            v (z + Function.update (0 : Cn n) j w) / w := hsupp.symm
      _ = (∫ w in Metric.ball (0 : ℂ) (2 * R),
            v (z + Function.update (0 : Cn n) j w) / w) - 0 := (sub_zero _).symm
      _ = (∫ w in Metric.ball (0 : ℂ) (2 * R),
            v (z + Function.update (0 : Cn n) j w) / w)
          - ∫ w in Metric.ball (0 : ℂ) (2 * R), v z / w := by rw [hcz0]
      _ = ∫ w in Metric.ball (0 : ℂ) (2 * R),
            (v (z + Function.update (0 : Cn n) j w) / w - v z / w) := step2.symm
      _ = ∫ w in Metric.ball (0 : ℂ) (2 * R),
            (fiberSlice j v z (z j + w) - fiberSlice j v z (z j)) / w := step1.symm
  rw [fiberPot_eq_shiftIntegral R j hvcont z, Work.CR.Flat.cauchyTransform, hmain]

end Work.NN.Core
