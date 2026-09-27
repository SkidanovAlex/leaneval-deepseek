import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# The `∂̄` of a mollifying convolution

For a `C¹` compactly supported real mollifier `ρ` and a `C¹` compactly supported test function `φ`,

  `∂̄ (fun y => ∫ t, ρ t * φ (y + t)) w = ∫ t, ρ t * ∂̄ φ (w + t)`,

i.e. `∂̄` commutes with the (reflected) mollification: `∂̄ (φ ⋆ ρᵣ) = (∂̄ φ) ⋆ ρᵣ` for `ρᵣ = ρ(-·)`.

Proof: differentiate under the integral sign with `hasFDerivAt_integral_of_dominated_of_fderiv_le`
(the domination bound comes from compactness of `tsupport ρ` and of a large ball containing
`w + tsupport ρ`), then read off the two values of the Fréchet derivative at `1` and `I` with
`ContinuousLinearMap.integral_apply`.
-/

set_option linter.unusedSimpArgs false

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.Mollify

/-- **The `∂̄` of a mollifying convolution.** -/
theorem dbar_convolution_eq {ρ : ℂ → ℝ} {φ : ℂ → ℂ}
    (hρc : ContDiff ℝ 1 ρ) (hρs : HasCompactSupport ρ)
    (hφc : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) (w : ℂ) :
    Work.Analysis.Complex.DbarCauchy.dbar (fun y => ∫ t, ρ t * φ (y + t)) w
      = ∫ t, ρ t * Work.Analysis.Complex.DbarCauchy.dbar φ (w + t) := by
  obtain ⟨Rρ, hRρ⟩ := hρs.isBounded.subset_closedBall (0 : ℂ)
  set Kl : Set ℂ := Metric.closedBall 0 (‖w‖ + 1 + Rρ) with hKldef
  have hKlc : IsCompact Kl := isCompact_closedBall (0 : ℂ) _
  have h1ne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hcontφ : Continuous φ := hφc.continuous
  have hcontf : Continuous (fderiv ℝ φ) := hφc.continuous_fderiv h1ne
  obtain ⟨Cφ, hCφ⟩ := hKlc.exists_bound_of_continuousOn hcontφ.continuousOn
  obtain ⟨Cf, hCf⟩ := hKlc.exists_bound_of_continuousOn hcontf.continuousOn
  have hρint : Integrable ρ volume := hρc.continuous.integrable_of_hasCompactSupport hρs
  have hnorm : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by
    simp [Complex.normSq, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
  have hmemKl : ∀ y ∈ Metric.closedBall w 1, ∀ t ∈ tsupport ρ, y + t ∈ Kl := by
    intro y hy t ht
    have hy1 : ‖y‖ ≤ ‖w‖ + 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      calc ‖y‖ = ‖(y - w) + w‖ := by ring_nf
        _ ≤ ‖y - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ 1 + ‖w‖ := by linarith
        _ = ‖w‖ + 1 := by ring
    have ht1 : ‖t‖ ≤ Rρ := by
      have h := hRρ ht
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    rw [hKldef, Metric.mem_closedBall, dist_zero_right]
    calc ‖y + t‖ ≤ ‖y‖ + ‖t‖ := norm_add_le _ _
      _ ≤ (‖w‖ + 1) + Rρ := by linarith
  set F : ℂ → ℂ → ℂ := fun y t => (ρ t : ℂ) * φ (y + t) with hFdef
  set F' : ℂ → ℂ → ℂ →L[ℝ] ℂ := fun y t => (ρ t : ℂ) • fderiv ℝ φ (y + t) with hF'def
  set bound : ℂ → ℝ := fun t => max Cf 0 * ‖ρ t‖ with hbounddef
  have hF_meas : ∀ᶠ x in 𝓝 w, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact ((Complex.measurable_ofReal.comp hρc.continuous.measurable).mul
      (hcontφ.measurable.comp (measurable_const.add measurable_id))).aestronglyMeasurable
  have hintF : Integrable (F w) volume := by
    refine Integrable.mono' (hρint.norm.const_mul (max Cφ 0)) hF_meas.self_of_nhds ?_
    filter_upwards with t
    by_cases ht : t ∈ tsupport ρ
    · have hb : ‖φ (w + t)‖ ≤ max Cφ 0 :=
        le_trans (hCφ _ (hmemKl w (Metric.mem_closedBall_self (by norm_num)) t ht))
          (le_max_left _ _)
      calc ‖F w t‖ = ‖(ρ t : ℂ)‖ * ‖φ (w + t)‖ := by rw [hFdef, norm_mul]
        _ = |ρ t| * ‖φ (w + t)‖ := by rw [hnorm]
        _ ≤ |ρ t| * max Cφ 0 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = max Cφ 0 * ‖ρ t‖ := by rw [Real.norm_eq_abs, mul_comm]
    · simp [hFdef, image_eq_zero_of_notMem_tsupport ht]
  have hF'_meas : AEStronglyMeasurable (F' w) volume := by
    refine ((hρc.continuous.measurable).smul
      (hcontf.measurable.comp (measurable_const.add measurable_id))).aestronglyMeasurable
  have h_bound : ∀ᵐ a : ℂ ∂volume, ∀ x ∈ Metric.closedBall w 1, ‖F' x a‖ ≤ bound a := by
    filter_upwards with a x hx
    by_cases ha : a ∈ tsupport ρ
    · have hb : ‖fderiv ℝ φ (x + a)‖ ≤ max Cf 0 :=
        le_trans (hCf _ (hmemKl x hx a ha)) (le_max_left _ _)
      calc ‖F' x a‖ = ‖(ρ a : ℂ)‖ * ‖fderiv ℝ φ (x + a)‖ := by
            rw [hF'def, norm_smul]
        _ = |ρ a| * ‖fderiv ℝ φ (x + a)‖ := by rw [hnorm]
        _ ≤ |ρ a| * max Cf 0 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = max Cf 0 * ‖ρ a‖ := by rw [Real.norm_eq_abs, mul_comm]
        _ = bound a := by rw [hbounddef]
    · simp [hF'def, hbounddef, image_eq_zero_of_notMem_tsupport ha]
  have h_integrable : Integrable bound volume := by
    rw [hbounddef]
    exact hρint.norm.const_mul (max Cf 0)
  have h_diff : ∀ᵐ a : ℂ ∂volume, ∀ x ∈ Metric.closedBall w 1,
      HasFDerivAt (fun y => F y a) (F' x a) x := by
    filter_upwards with a x _
    have hφd : Differentiable ℝ φ := hφc.differentiable h1ne
    have h1 : HasFDerivAt (fun y : ℂ => φ (y + a)) (fderiv ℝ φ (x + a)) x := by
      have h := (hφd (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    have h2 := h1.const_mul ((ρ a : ℂ))
    simpa only [hFdef, hF'def] using h2
  have hΨ : HasFDerivAt (fun y => ∫ t, F y t) (∫ t, F' w t) w :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (𝕜 := ℝ)
      (F := F) (F' := F') (bound := bound) (s := Metric.closedBall w 1) (x₀ := w)
      (Metric.closedBall_mem_nhds w (by norm_num)) hF_meas hintF hF'_meas h_bound
      h_integrable h_diff
  have hF'w_int : Integrable (F' w) volume := by
    refine Integrable.mono' h_integrable hF'_meas ?_
    filter_upwards [h_bound] with a ha
    exact ha w (Metric.mem_closedBall_self (by norm_num))
  have hA_int : Integrable (fun t : ℂ => (F' w t) 1) volume :=
    ContinuousLinearMap.integrable_comp (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)) hF'w_int
  have hB_int : Integrable (fun t : ℂ => (F' w t) Complex.I) volume :=
    ContinuousLinearMap.integrable_comp (ContinuousLinearMap.apply ℝ ℂ Complex.I) hF'w_int
  have hfun : (fun y : ℂ => ∫ t, ρ t * φ (y + t)) = (fun y => ∫ t, F y t) := rfl
  have hL : Work.Analysis.Complex.DbarCauchy.dbar (fun y => ∫ t, ρ t * φ (y + t)) w
      = (∫ t, (F' w t) 1) + Complex.I * (∫ t, (F' w t) Complex.I) := by
    rw [hfun, Work.Analysis.Complex.DbarCauchy.dbar, hΨ.fderiv,
      ContinuousLinearMap.integral_apply hF'w_int (1 : ℂ),
      ContinuousLinearMap.integral_apply hF'w_int Complex.I]
  have hR : (∫ t, ρ t * Work.Analysis.Complex.DbarCauchy.dbar φ (w + t))
      = (∫ t, (F' w t) 1) + Complex.I * (∫ t, (F' w t) Complex.I) := by
    calc ∫ t, ρ t * Work.Analysis.Complex.DbarCauchy.dbar φ (w + t)
        = ∫ t, ((F' w t) 1 + Complex.I * ((F' w t) Complex.I)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            simp only [hF'def, Work.Analysis.Complex.DbarCauchy.dbar,
              ContinuousLinearMap.smul_apply]
            ring
      _ = (∫ t, (F' w t) 1) + ∫ t, Complex.I * ((F' w t) Complex.I) :=
            MeasureTheory.integral_add hA_int (hB_int.const_mul Complex.I)
      _ = (∫ t, (F' w t) 1) + Complex.I * (∫ t, (F' w t) Complex.I) := by
            rw [MeasureTheory.integral_const_mul]
  rw [hL, hR]

end Work.Analysis.Complex.Mollify
