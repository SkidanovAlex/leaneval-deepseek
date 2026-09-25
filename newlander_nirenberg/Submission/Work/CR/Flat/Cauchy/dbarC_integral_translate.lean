import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Differentiation under the integral sign for the Cauchy potential: for `C¹` `f` the map
`z ↦ ∫_{‖w‖<ρ} (f (z+w) - f z)/w` is real differentiable at every `z` with real differential
`∫_{‖w‖<ρ} w⁻¹ • (fderiv ℝ f (z+w) - fderiv ℝ f z)`, hence `∂̄`-derivative
`∫_{‖w‖<ρ} (∂̄f (z+w) - ∂̄f z)/w`. -/
theorem dbarC_integral_translate {ρ : ℝ} {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (z : ℂ) :
    Work.CR.Flat.dbarC (fun z : ℂ => ∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w) z
      = ∫ w in Metric.ball (0 : ℂ) ρ,
          (Work.CR.Flat.dbarC f (z + w) - Work.CR.Flat.dbarC f z) / w := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [Metric.ball_eq_empty.mpr hρ]
    simp [Work.CR.Flat.dbarC]
  · have hρpos : 0 < ρ := hρ
    have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
    have hderiv_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
    obtain ⟨C, hC⟩ := (isCompact_closedBall z (1 + ρ)).exists_bound_of_continuousOn
      hderiv_cont.continuousOn
    have hCz : ‖fderiv ℝ f z‖ ≤ C := hC z (by rw [Metric.mem_closedBall, dist_self]; linarith)
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) hCz
    set μ : Measure ℂ := volume.restrict (Metric.ball (0 : ℂ) ρ) with hμdef
    have hmeasF : ∀ x : ℂ, AEStronglyMeasurable (fun w : ℂ => (f (x + w) - f x) / w) μ := by
      intro x
      have hm : Measurable (fun w : ℂ => (f (x + w) - f x) * w⁻¹) :=
        ((hf.continuous.measurable.comp (continuous_const.add continuous_id).measurable).sub
          measurable_const).mul measurable_inv
      simpa [div_eq_mul_inv] using hm.aestronglyMeasurable
    have hmeasF' : AEStronglyMeasurable
        (fun w : ℂ => w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) μ := by
      have hm : Measurable (fun w : ℂ => w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) :=
        measurable_inv.smul
          ((hderiv_cont.measurable.comp (continuous_const.add continuous_id).measurable).sub
            measurable_const)
      exact hm.aestronglyMeasurable
    obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall z ρ) (isCompact_closedBall z ρ)
    have hKbound : ∀ w ∈ Metric.ball (0 : ℂ) ρ, ‖f (z + w) - f z‖ ≤ (K : ℝ) * ‖w‖ := by
      intro w hw
      have hz : z ∈ Metric.closedBall z ρ := by rw [Metric.mem_closedBall, dist_self]; linarith
      have hzw : z + w ∈ Metric.closedBall z ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        exact le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hw)
      have hdist := hK.dist_le_mul z hz (z + w) hzw
      rw [dist_eq_norm, dist_eq_norm] at hdist
      rw [show z - (z + w) = -w by ring, norm_neg] at hdist
      calc ‖f (z + w) - f z‖ = ‖f z - f (z + w)‖ := norm_sub_rev _ _
        _ ≤ (K : ℝ) * ‖w‖ := hdist
    have hF_int : Integrable (fun w : ℂ => (f (z + w) - f z) / w) μ := by
      refine Integrable.mono'
        ((integrableOn_norm_rpow_ball (s := 0) (by norm_num : (-2 : ℝ) < 0)).const_mul (K : ℝ))
        (hmeasF z) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw
      rw [Real.rpow_zero, mul_one]
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hw0)]
        exact hKbound w hw
    have hbound_int : Integrable (fun w : ℂ => 2 * C * ‖w‖ ^ (-1 : ℝ)) μ :=
      (integrableOn_norm_rpow_ball (s := -1) (by norm_num : (-2 : ℝ) < -1)).const_mul (2 * C)
    have h_bound : ∀ᵐ a ∂μ, ∀ x ∈ Metric.ball z 1,
        ‖a⁻¹ • (fderiv ℝ f (x + a) - fderiv ℝ f x)‖ ≤ 2 * C * ‖a‖ ^ (-1 : ℝ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with a ha x hx
      have hxmem : x ∈ Metric.closedBall z (1 + ρ) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : ‖x - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hx
        linarith
      have hxamem : x + a ∈ Metric.closedBall z (1 + ρ) := by
        rw [Metric.mem_closedBall, dist_eq_norm, show x + a - z = (x - z) + a by ring]
        have h1 : ‖x - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hx
        have h2 : ‖a‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp ha
        exact le_of_lt (calc ‖(x - z) + a‖ ≤ ‖x - z‖ + ‖a‖ := norm_add_le _ _
          _ < 1 + ρ := by linarith)
      have hD : ‖fderiv ℝ f (x + a) - fderiv ℝ f x‖ ≤ 2 * C := by
        calc ‖fderiv ℝ f (x + a) - fderiv ℝ f x‖
            ≤ ‖fderiv ℝ f (x + a)‖ + ‖fderiv ℝ f x‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (hC _ hxamem) (hC _ hxmem)
          _ = 2 * C := by ring
      rw [norm_smul, norm_inv, Real.rpow_neg_one]
      exact (mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr (norm_nonneg a))).trans
        (le_of_eq (by ring))
    have h_diff : ∀ᵐ a ∂μ, ∀ x ∈ Metric.ball z 1,
        HasFDerivAt (fun y : ℂ => (f (y + a) - f y) / a)
          (a⁻¹ • (fderiv ℝ f (x + a) - fderiv ℝ f x)) x :=
      Filter.Eventually.of_forall (fun a x _ => by
        have hshift : HasFDerivAt (fun y : ℂ => y + a) (ContinuousLinearMap.id ℝ ℂ) x :=
          (hasFDerivAt_id (𝕜 := ℝ) x).add_const a
        have h1 : HasFDerivAt (fun y : ℂ => f (y + a)) (fderiv ℝ f (x + a)) x := by
          have h := (hf_diff.differentiableAt.hasFDerivAt).comp x hshift
          rwa [ContinuousLinearMap.comp_id] at h
        have h2 : HasFDerivAt f (fderiv ℝ f x) x := hf_diff.differentiableAt.hasFDerivAt
        have h3 := h1.sub h2
        have h4 := h3.mul_const (a⁻¹)
        simpa [div_eq_mul_inv, Pi.sub_apply] using h4)
    have hdiff : HasFDerivAt (fun x : ℂ => ∫ w in Metric.ball (0 : ℂ) ρ, (f (x + w) - f x) / w)
        (∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) z :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (α := ℂ) (E := ℂ) (H := ℂ)
        (μ := μ) (F := fun x w => (f (x + w) - f x) / w)
        (F' := fun x w => w⁻¹ • (fderiv ℝ f (x + w) - fderiv ℝ f x))
        (bound := fun w => 2 * C * ‖w‖ ^ (-1 : ℝ))
        (s := Metric.ball z 1) (x₀ := z) (Metric.ball_mem_nhds z one_pos)
        (Filter.Eventually.of_forall hmeasF) hF_int hmeasF' h_bound hbound_int h_diff
    have hfd : fderiv ℝ (fun x : ℂ => ∫ w in Metric.ball (0 : ℂ) ρ, (f (x + w) - f x) / w) z
        = ∫ w in Metric.ball (0 : ℂ) ρ, w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z) :=
      hdiff.fderiv
    have hInt : Integrable (fun w : ℂ => w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) μ :=
      hbound_int.mono' hmeasF' (h_bound.mono (fun a ha => ha z (Metric.mem_ball_self one_pos)))
    have h1int : Integrable (fun w : ℂ => (w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) 1) μ :=
      hInt.apply_continuousLinearMap 1
    have h2int : Integrable
        (fun w : ℂ => Complex.I * ((w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) Complex.I)) μ :=
      (hInt.apply_continuousLinearMap Complex.I).const_mul Complex.I
    have hpt : ∀ w : ℂ,
        (Work.CR.Flat.dbarC f (z + w) - Work.CR.Flat.dbarC f z) / w
          = (1 / 2) * ((w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) 1
              + Complex.I * ((w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) Complex.I)) := by
      intro w
      simp only [Work.CR.Flat.dbarC, smul_apply, sub_apply, smul_eq_mul]
      ring
    have hRHS : (∫ w in Metric.ball (0 : ℂ) ρ,
          (Work.CR.Flat.dbarC f (z + w) - Work.CR.Flat.dbarC f z) / w)
        = (1 / 2) * ((∫ w in Metric.ball (0 : ℂ) ρ,
              w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) 1
            + Complex.I * (∫ w in Metric.ball (0 : ℂ) ρ,
              w⁻¹ • (fderiv ℝ f (z + w) - fderiv ℝ f z)) Complex.I) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      rw [ContinuousLinearMap.integral_apply hInt 1,
        ContinuousLinearMap.integral_apply hInt Complex.I]
      rw [← integral_const_mul]
      rw [← integral_add h1int h2int]
      rw [← integral_const_mul]
    rw [hRHS]
    conv_lhs => rw [Work.CR.Flat.dbarC, hfd]

end Work.CR.Flat.Cauchy
