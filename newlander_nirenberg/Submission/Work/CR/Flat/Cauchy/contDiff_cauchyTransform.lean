import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.cauchyTransform_eq_unsub

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal Convolution
open MeasureTheory Set

/-!
## The Cauchy potential as a convolution

`cauchyTransform ρ f z = -(1/π) ∫_{‖w‖<ρ} (f (z+w) - f z)/w` is the convolution of `f`
against the compactly supported, integrable kernel
`cauchyBallKernel ρ w = (1/π) 1_{‖w‖<ρ} w⁻¹`.

Indeed, for continuous `f` the subtracted integral equals the integral of `f (z+w)/w`
(the constant `f z` drops out by the symmetry `∫_{‖w‖<ρ} 1/w = 0`), and reindexing
`w ↦ -w` (which preserves the disc) turns `∫_{‖w‖<ρ} f (z+w)/w` into
`(cauchyBallKernel ρ ⋆ f) z = ∫_{t, ‖t‖<ρ} (1/π) f (z-t)/t`.

Consequently `ContDiff ℝ n f → ContDiff ℝ n (T f)` for every `n`, by the general
smoothness of the convolution of a compactly supported `Cⁿ` function with an
integrable kernel (`HasCompactSupport.contDiff_convolution_right`).
-/

/-- Negation preserves the disc `‖x‖ < ρ` and Lebesgue measure:
`∫_{‖x‖<ρ} g (-x) = ∫_{‖x‖<ρ} g x`. -/
lemma setIntegral_neg_ball (ρ : ℝ) (g : ℂ → ℂ) :
    ∫ x in Metric.ball (0 : ℂ) ρ, g (-x) = ∫ x in Metric.ball (0 : ℂ) ρ, g x := by
  have h := MeasurableEmbedding.setIntegral_map (μ := (volume : Measure ℂ))
    measurableEmbedding_neg g (Metric.ball (0 : ℂ) ρ)
  rw [Measure.map_neg_eq_self (volume : Measure ℂ)] at h
  have hpre : (Neg.neg ⁻¹' Metric.ball (0 : ℂ) ρ : Set ℂ) = Metric.ball (0 : ℂ) ρ := by
    ext x
    simp [Metric.mem_ball, dist_zero_right]
  rw [hpre] at h
  exact h.symm

/-- The compactly supported Cauchy kernel `w ↦ (1/π)·1_{‖w‖<ρ}·w⁻¹`. -/
noncomputable def cauchyBallKernel (ρ : ℝ) : ℂ → ℂ :=
  (Metric.ball (0 : ℂ) ρ).indicator (fun w => ((Real.pi : ℂ))⁻¹ * w⁻¹)

@[simp] lemma cauchyBallKernel_of_mem {ρ : ℝ} {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) ρ) :
    cauchyBallKernel ρ w = ((Real.pi : ℂ))⁻¹ * w⁻¹ :=
  Set.indicator_of_mem hw _

@[simp] lemma cauchyBallKernel_of_notMem {ρ : ℝ} {w : ℂ} (hw : w ∉ Metric.ball (0 : ℂ) ρ) :
    cauchyBallKernel ρ w = 0 :=
  Set.indicator_of_notMem hw _

/-- The Cauchy kernel of a disc is integrable: it is the constant `1/π` times
`(ball 0 ρ).indicator (fun w => w⁻¹)`, and `w ↦ w⁻¹` is integrable on the disc. -/
lemma integrable_cauchyBallKernel (ρ : ℝ) :
    Integrable (cauchyBallKernel ρ) (volume : Measure ℂ) :=
  (integrable_indicator_iff measurableSet_ball).mpr ((integrableOn_inv_ball ρ).const_mul _)

/-- For continuous `f`, the "unsubtracted" Cauchy integrand `w ↦ f (z+w)/w` is integrable
on any disc: `f (z+·)` is bounded there and `w ↦ ‖w‖⁻¹` is integrable. -/
lemma integrableOn_shifted_div {ρ : ℝ} {f : ℂ → ℂ} (hf : Continuous f) (z : ℂ) :
    IntegrableOn (fun w : ℂ => f (z + w) / w) (Metric.ball (0 : ℂ) ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hf.comp (continuous_const.add continuous_id)).continuousOn
  have hmaj : IntegrableOn (fun w : ℂ => C * ‖w⁻¹‖) (Metric.ball (0 : ℂ) ρ) :=
    (integrableOn_inv_ball ρ).norm.const_mul C
  refine hmaj.mono' ?_ ?_
  · exact ((hf.comp (continuous_const.add continuous_id)).measurable.div
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    rw [norm_div]
    calc ‖f (z + w)‖ / ‖w‖ = ‖f (z + w)‖ * ‖w⁻¹‖ := by rw [norm_inv, div_eq_mul_inv]
      _ ≤ C * ‖w⁻¹‖ :=
          mul_le_mul_of_nonneg_right (hC w (Metric.ball_subset_closedBall hw)) (norm_nonneg _)

/-- The Cauchy potential of a continuous function is the convolution of `f` with the
compactly supported kernel `cauchyBallKernel ρ`. -/
lemma cauchyTransform_eq_convolution {ρ : ℝ} {f : ℂ → ℂ} (hf : Continuous f) (z : ℂ) :
    cauchyTransform ρ f z
      = (cauchyBallKernel ρ ⋆[ContinuousLinearMap.mul ℝ ℂ, (volume : Measure ℂ)] f) z := by
  have hint := integrableOn_shifted_div (ρ := ρ) hf z
  rw [cauchyTransform_eq_unsub hint]
  simp only [cauchyTransformUnsub]
  -- The subtracted integral equals the unsubtracted one, and reindexing `w ↦ -w` flips it.
  have hneg : (∫ w in Metric.ball (0 : ℂ) ρ, f (z + w) / w)
      = - ∫ t in Metric.ball (0 : ℂ) ρ, f (z - t) / t := by
    have h := setIntegral_neg_ball ρ (fun y : ℂ => f (z + y) / y)
    rw [show (fun x : ℂ => f (z + -x) / -x) = fun x : ℂ => -(f (z - x) / x) by
      funext x; rw [sub_eq_add_neg, div_neg]] at h
    rw [integral_neg] at h
    exact h.symm
  -- Expand the convolution: it is `(1/π) ∫_{‖t‖<ρ} f (z-t)/t`.
  have hK : (∫ t, cauchyBallKernel ρ t * f (z - t))
      = ((Real.pi : ℂ))⁻¹ * ∫ t in Metric.ball (0 : ℂ) ρ, f (z - t) / t := by
    have h1 : (∫ t, cauchyBallKernel ρ t * f (z - t))
        = ∫ t, (Metric.ball (0 : ℂ) ρ).indicator
            (fun t : ℂ => ((Real.pi : ℂ))⁻¹ * (t⁻¹ * f (z - t))) t := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Metric.ball (0 : ℂ) ρ
      · rw [cauchyBallKernel_of_mem ht, Set.indicator_of_mem ht, mul_assoc]
      · rw [cauchyBallKernel_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [h1, integral_indicator measurableSet_ball, integral_const_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro t _
    dsimp only
    rw [div_eq_mul_inv, mul_comm]
  rw [hneg]
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']
  rw [hK]
  ring

theorem contDiff_cauchyTransform {ρ : ℝ} {n : ℕ∞} {f : ℂ → ℂ} (hf : ContDiff ℝ n f)
    (hfsupp : SupportedInBall (ρ / 2) f) : ContDiff ℝ n (cauchyTransform ρ f) := by
  have hcont : Continuous f := hf.continuous
  have hcomp : HasCompactSupport f := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) (ρ / 2))
      (isCompact_closedBall (0 : ℂ) (ρ / 2)) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hfsupp x (le_of_lt (not_le.mp hx))
  have hK : LocallyIntegrable (cauchyBallKernel ρ) (volume : Measure ℂ) :=
    (integrable_cauchyBallKernel ρ).locallyIntegrable
  have heq : cauchyTransform ρ f
      = cauchyBallKernel ρ ⋆[ContinuousLinearMap.mul ℝ ℂ, (volume : Measure ℂ)] f :=
    funext fun z => cauchyTransform_eq_convolution hcont z
  rw [heq]
  exact HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hcomp hK hf

end Work.CR.Flat.Cauchy
