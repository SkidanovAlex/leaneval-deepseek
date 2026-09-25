/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Differentiability of the annulus potential `fiberPotAnn`

This file proves that the `l`-th fixed-disc fibre potential

  `fiberPotAnn j l (fiberAnnulus (s j) R) η z
      = -(1/π) ∫_{w ∈ fiberAnnulus (s j) R} η (z with z j := w) (w - z j)^{-(l+1)} dw`

is differentiable on the polydisc `polydisc 0 r`, for `C^1` data `η` and radii
`r < s < R` (componentwise `r i < s i`, and `s j < R`).

The point is exactly the same one that makes the potential continuous
(`continuousOn_fiberPotAnn`): on `polydisc 0 r` the pole `z j` stays at positive distance
`δ = (s j - r j)/2` from the annulus `fiberAnnulus (s j) R`, so the integrand is a
`C^1` function of the base point and differentiation under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) applies.  The uniform domination is
supplied by the compactness of the set of inserted points
`{(z with z j := w) | ‖z - x‖ ≤ δ, ‖w‖ ≤ R}`, on which `η` and `fderiv ℝ η` are bounded.

-/
import Mathlib
import Submission.Work.NN.Core.VanishingDefs
import Submission.Work.NN.Core.fderiv_fiberPotAnn_apply

noncomputable section

open scoped NNReal ENNReal
open scoped Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

/-- The integrand of the annulus potential. -/
private def annIntegrandNN {n : ℕ} (j : Fin n) (l : ℕ) (η : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) : ℂ :=
  η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)

/-- The candidate derivative of the integrand in the base point. -/
private def annDerivNN {n : ℕ} (j : Fin n) (l : ℕ) (η : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (w : ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  (η (Function.update z j w)) • (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))
    + (((w - z j)⁻¹) ^ (l + 1)) • ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))

/-- The map inserting `w` in the `j`-th coordinate is continuous in `w`. -/
private lemma cont_update_right {n : ℕ} (j : Fin n) (z : Fin n → ℂ) :
    Continuous fun w : ℂ => Function.update z j w :=
  Continuous.update continuous_const j continuous_id

/-- **Differentiability of the annulus potential.**  For `C^1` data `η` and radii
`r < s < R`, the `l`-th fixed-disc fibre potential over the annulus `fiberAnnulus (s j) R`
is differentiable at every point of `polydisc 0 r`. -/
theorem differentiableAt_fiberPotAnn {n : ℕ} {j : Fin n} {l : ℕ} {R : ℝ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : (Fin n → ℂ) → ℂ} (hη : ContDiff ℝ 1 η)
    {x : Fin n → ℂ} (hx : x ∈ Work.CR.Flat.polydisc 0 r) :
    DifferentiableAt ℝ (fiberPotAnn j l (fiberAnnulus (s j) R) η) x := by
  have hxj : ‖x j‖ < r j := by simpa using hx j
  have hd : 0 < s j - r j := by linarith [hr j, hrs j]
  have hR0 : 0 < R := lt_trans (lt_trans (hr j) (hrs j)) hsR
  -- the radius of the neighbourhood on which the pole stays away from the annulus
  set δ : ℝ := (s j - r j) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hxδ : ‖x j‖ + δ < s j := by
    rw [hδdef]; nlinarith [hxj, hrs j]
  have hηc : Continuous η := hη.continuous
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hηdc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hAmeas : MeasurableSet (fiberAnnulus (s j) R) := measurableSet_fiberAnnulus (s j) R
  have hAfin : volume (fiberAnnulus (s j) R) < ⊤ := volume_fiberAnnulus_lt_top (s j) R
  have hfinm : IsFiniteMeasure (volume.restrict (fiberAnnulus (s j) R)) :=
    isFiniteMeasure_restrict_of_lt_top hAfin
  -- the compact set of all inserted points relevant near `x`
  set K : Set (Fin n → ℂ) :=
    (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j p.2) ''
      (Metric.closedBall x δ ×ˢ Metric.closedBall (0 : ℂ) R) with hK
  have hKcomp : IsCompact K :=
    ((isCompact_closedBall x δ).prod (isCompact_closedBall (0 : ℂ) R)).image
      (_root_.continuous_update (i := j))
  obtain ⟨M, hM⟩ := hKcomp.exists_bound_of_continuousOn hηc.continuousOn
  obtain ⟨M', hM'⟩ := hKcomp.exists_bound_of_continuousOn hηdc.continuousOn
  have hKne : K.Nonempty :=
    ⟨Function.update x j 0, (x, 0), ⟨by simpa using hδpos.le, by simpa using hR0.le⟩, rfl⟩
  obtain ⟨y0, hy0⟩ := hKne
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (η y0)) (hM y0 hy0)
  have hM'nn : 0 ≤ M' := le_trans (norm_nonneg (fderiv ℝ η y0)) (hM' y0 hy0)
  have hzm : ∀ z ∈ Metric.ball x δ, z ∈ Metric.closedBall x δ :=
    fun z hz => Metric.ball_subset_closedBall hz
  have hAclosed : fiberAnnulus (s j) R ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    rw [mem_fiberAnnulus] at hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw.2.le
  have hupdK : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R,
      Function.update z j w ∈ K := by
    intro z hz w hw
    exact ⟨(z, w), ⟨hzm z hz, hAclosed hw⟩, rfl⟩
  have hηbd : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R,
      ‖η (Function.update z j w)‖ ≤ M := fun z hz w hw => hM _ (hupdK z hz w hw)
  have hη'bd : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R,
      ‖fderiv ℝ η (Function.update z j w)‖ ≤ M' := fun z hz w hw => hM' _ (hupdK z hz w hw)
  -- control of the `j`-th coordinate and separation from the annulus
  have hzj_lt : ∀ z ∈ Metric.ball x δ, ‖z j‖ < ‖x j‖ + δ := by
    intro z hz
    have hdist : ‖z - x‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc ‖z j‖ = ‖(z j - x j) + x j‖ := by ring_nf
      _ ≤ ‖z j - x j‖ + ‖x j‖ := norm_add_le _ _
      _ ≤ ‖z - x‖ + ‖x j‖ := by
            have h := norm_le_pi_norm (z - x) j
            exact add_le_add_left h (‖x j‖)
      _ < δ + ‖x j‖ := by linarith
      _ = ‖x j‖ + δ := by ring
  have hzs : ∀ z ∈ Metric.ball x δ, ‖z j‖ < s j := by
    intro z hz
    have := hzj_lt z hz
    linarith [hxδ]
  have hsep : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R, δ ≤ ‖w - z j‖ := by
    intro z hz w hw
    rw [mem_fiberAnnulus] at hw
    have h1 := hzj_lt z hz
    have h3 : δ < s j - (‖x j‖ + δ) := by rw [hδdef]; nlinarith [hxj, hrs j]
    have h4 : s j - ‖z j‖ ≤ ‖w‖ - ‖z j‖ := by linarith [hw.1]
    have h5 : ‖w‖ - ‖z j‖ ≤ ‖w - z j‖ := norm_sub_norm_le w (z j)
    linarith
  -- the kernel bounds on the annulus
  have hk1 : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R,
      ‖((w - z j)⁻¹) ^ (l + 1)‖ ≤ (δ⁻¹) ^ (l + 1) := by
    intro z hz w hw
    calc ‖((w - z j)⁻¹) ^ (l + 1)‖ = ‖(w - z j)⁻¹‖ ^ (l + 1) := norm_pow _ _
      _ = (‖w - z j‖⁻¹) ^ (l + 1) := by rw [norm_inv]
      _ ≤ (δ⁻¹) ^ (l + 1) :=
          pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hδpos (hsep z hz w hw)) _
  have hk2 : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R,
      ‖((w - z j)⁻¹) ^ (l + 2)‖ ≤ (δ⁻¹) ^ (l + 2) := by
    intro z hz w hw
    calc ‖((w - z j)⁻¹) ^ (l + 2)‖ = ‖(w - z j)⁻¹‖ ^ (l + 2) := norm_pow _ _
      _ = (‖w - z j‖⁻¹) ^ (l + 2) := by rw [norm_inv]
      _ ≤ (δ⁻¹) ^ (l + 2) :=
          pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hδpos (hsep z hz w hw)) _
  have hcompbd : ∀ z ∈ Metric.ball x δ, ∀ w ∈ fiberAnnulus (s j) R,
      ‖(fderiv ℝ η (Function.update z j w)).comp (updateZero j)‖ ≤ M' := by
    intro z hz w hw
    calc ‖(fderiv ℝ η (Function.update z j w)).comp (updateZero j)‖
        ≤ ‖fderiv ℝ η (Function.update z j w)‖ * ‖updateZero j‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M' * 1 := mul_le_mul (hη'bd z hz w hw) (norm_updateZero_le j) (norm_nonneg _) hM'nn
      _ = M' := mul_one M'
  -- the dominating constant
  set C : ℝ := M * (‖(l + 1 : ℂ)‖ * (δ⁻¹) ^ (l + 2)) + M' * (δ⁻¹) ^ (l + 1) with hCdef
  have hbound : ∀ᵐ w ∂(volume.restrict (fiberAnnulus (s j) R)),
      ∀ z ∈ Metric.ball x δ, ‖annDerivNN j l η z w‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict hAmeas] with w hw z hz
    have hb1 : ‖(η (Function.update z j w)) •
        (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
        ≤ M * (‖(l + 1 : ℂ)‖ * (δ⁻¹) ^ (l + 2)) := by
      calc ‖(η (Function.update z j w)) •
            (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
          ≤ ‖η (Function.update z j w)‖ *
              ‖(((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖ :=
            norm_smul_clm_le _ _
        _ ≤ M * (‖(l + 1 : ℂ)‖ * (δ⁻¹) ^ (l + 2)) := by
            refine mul_le_mul (hηbd z hz w hw) ?_ (norm_nonneg _) hMnn
            refine le_trans (norm_smul_clm_le _ _) ?_
            refine le_trans (mul_le_mul_of_nonneg_left (norm_coordCLM_le j) (norm_nonneg _)) ?_
            rw [mul_one, norm_mul]
            exact mul_le_mul_of_nonneg_left (hk2 z hz w hw) (norm_nonneg _)
    have hb2 : ‖(((w - z j)⁻¹) ^ (l + 1)) •
        ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))‖
        ≤ M' * (δ⁻¹) ^ (l + 1) := by
      refine le_trans (norm_smul_clm_le _ _) ?_
      calc ‖((w - z j)⁻¹) ^ (l + 1)‖ *
            ‖(fderiv ℝ η (Function.update z j w)).comp (updateZero j)‖
          ≤ (δ⁻¹) ^ (l + 1) * M' :=
            mul_le_mul (hk1 z hz w hw) (hcompbd z hz w hw) (norm_nonneg _) (by positivity)
        _ = M' * (δ⁻¹) ^ (l + 1) := by ring
    calc ‖annDerivNN j l η z w‖
        ≤ ‖(η (Function.update z j w)) •
              (((l + 1 : ℂ) * ((w - z j)⁻¹) ^ (l + 2)) • (coordCLM j))‖
          + ‖(((w - z j)⁻¹) ^ (l + 1)) •
              ((fderiv ℝ η (Function.update z j w)).comp (updateZero j))‖ := by
          rw [annDerivNN]; exact norm_add_le _ _
      _ ≤ C := by rw [hCdef]; linarith
  -- the pointwise derivative of the integrand
  have hdiff : ∀ᵐ w ∂(volume.restrict (fiberAnnulus (s j) R)),
      ∀ z ∈ Metric.ball x δ,
        HasFDerivAt (fun z : Fin n → ℂ => annIntegrandNN j l η z w) (annDerivNN j l η z w) z := by
    filter_upwards [self_mem_ae_restrict hAmeas] with w hw z hz
    have hwne : w ≠ z j := by
      intro h
      have hle : s j ≤ ‖w‖ := (mem_fiberAnnulus.mp hw).1
      have hlt := hzs z hz
      rw [h] at hle
      linarith
    have h1 : HasFDerivAt (fun y : Fin n → ℂ => η (Function.update y j w))
        ((fderiv ℝ η (Function.update z j w)).comp (updateZero j)) z :=
      (hηd.differentiableAt.hasFDerivAt).comp z (hasFDerivAt_update_ann j w z)
    have h2 := hasFDerivAt_inv_pow_update j l w hwne (x := z)
    have h3 := h1.mul h2
    have hfe : (fun y : Fin n → ℂ => η (Function.update y j w) * ((w - y j)⁻¹) ^ (l + 1))
        =ᶠ[𝓝 z] ((fun y : Fin n → ℂ => η (Function.update y j w)) *
          fun y => ((w - y j)⁻¹) ^ (l + 1)) :=
      Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]
    have h4 := (hfe.hasFDerivAt_iff).mpr h3
    simpa only [annIntegrandNN, annDerivNN] using h4
  have hxball : x ∈ Metric.ball x δ := Metric.mem_ball_self hδpos
  -- integrability of the integrand at the base point
  have hFint : Integrable (fun w => annIntegrandNN j l η x w)
      (volume.restrict (fiberAnnulus (s j) R)) := by
    refine MeasureTheory.Integrable.of_bound ?_ (M * (δ⁻¹) ^ (l + 1)) ?_
    · exact (((hηc.measurable.comp (cont_update_right j x).measurable)).mul
        (((measurable_id.sub measurable_const).inv).pow_const (l + 1))).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict hAmeas] with w hw
      simp only [annIntegrandNN]
      calc ‖η (Function.update x j w) * ((w - x j)⁻¹) ^ (l + 1)‖
          = ‖η (Function.update x j w)‖ * ‖((w - x j)⁻¹) ^ (l + 1)‖ := norm_mul _ _
        _ ≤ M * (δ⁻¹) ^ (l + 1) :=
            mul_le_mul (hηbd x hxball w hw) (hk1 x hxball w hw) (norm_nonneg _) hMnn
  have hFmeas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable
      (fun w => annIntegrandNN j l η z w) (volume.restrict (fiberAnnulus (s j) R)) :=
    Filter.Eventually.of_forall fun z => by
      simp only [annIntegrandNN]
      exact (((hηc.measurable.comp (cont_update_right j z).measurable)).mul
        (((measurable_id.sub measurable_const).inv).pow_const (l + 1))).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun w => annDerivNN j l η x w)
      (volume.restrict (fiberAnnulus (s j) R)) := by
    have hmeas : Measurable (fun w : ℂ => annDerivNN j l η x w) := by
      simp only [annDerivNN]
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hCint : Integrable (fun _ : ℂ => C) (volume.restrict (fiberAnnulus (s j) R)) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr inferInstance
  -- differentiation under the integral sign
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume.restrict (fiberAnnulus (s j) R))
    (F := fun z w => annIntegrandNN j l η z w)
    (F' := fun z w => annDerivNN j l η z w)
    (x₀ := x) (bound := fun _ => C) (s := Metric.ball x δ)
    (Metric.ball_mem_nhds x hδpos) hFmeas hFint hF'meas hbound hCint hdiff
  have hpot : fiberPotAnn j l (fiberAnnulus (s j) R) η
      = fun z => -((Real.pi : ℂ))⁻¹ * ∫ w, annIntegrandNN j l η z w
          ∂(volume.restrict (fiberAnnulus (s j) R)) := by
    funext z
    rw [fiberPotAnn_apply]
    rfl
  refine ⟨-((Real.pi : ℂ))⁻¹ • (∫ w, annDerivNN j l η x w
      ∂(volume.restrict (fiberAnnulus (s j) R))), ?_⟩
  rw [hpot]
  exact hmain.const_mul _

theorem differentiableOn_fiberPotAnn {n : ℕ} {j : Fin n} {l : ℕ} {R : ℝ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R) :
    ∀ η : (Fin n → ℂ) → ℂ, ContDiff ℝ 1 η →
      DifferentiableOn ℝ (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc 0 r) := by
  intro η hη x hx
  exact (differentiableAt_fiberPotAnn hr hrs hsR hη hx).differentiableWithinAt

end Work.NN.Core
