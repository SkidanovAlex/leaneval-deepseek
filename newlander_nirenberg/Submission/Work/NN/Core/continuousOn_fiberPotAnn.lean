import Mathlib
import Submission.Work.NN.Core.VanishingDefs

noncomputable section

open scoped NNReal ENNReal
open scoped Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

/-- **Continuity of the annulus potential.**  For arbitrary *continuous* data `η`, the `l`-th
fixed-disc fibre potential `fiberPotAnn j l (fiberAnnulus (s j) R) η` is continuous on the polydisc
`polydisc 0 r`, provided `r < s < R` in the relevant sense (`r i < s i` for every `i` and
`s j < R`).  No vanishing of `η` is needed: on `polydisc 0 r` the pole `z j` stays inside the
``inner disc'' `‖z j‖ < r j < s j` of the annulus, so the kernel `(w - z j)^{-(l+1)}` is continuous
and bounded on the (bounded, finite measure) annulus, and continuity follows from the dominated
convergence theorem applied to the parametrised integral. -/
theorem continuousOn_fiberPotAnn {n : ℕ} {j : Fin n} {l : ℕ} {R : ℝ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R) :
    ∀ η : (Fin n → ℂ) → ℂ, Continuous η →
      ContinuousOn (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc 0 r) := by
  intro η hη
  have hd : 0 < s j - r j := by linarith [hr j, hrs j]
  have hR0 : 0 < R := lt_trans (lt_trans (hr j) (hrs j)) hsR
  intro z0 hz0
  -- a polydisc neighbourhood of the base point, on which the pole stays off the annulus
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp
    ((Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) r).mem_nhds hz0)
  -- the compact set of all inserted points relevant near `z0`
  set K : Set (Fin n → ℂ) :=
    (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 j p.2) ''
      (Metric.closedBall z0 δ ×ˢ Metric.closedBall (0 : ℂ) R) with hK
  have hKcomp : IsCompact K :=
    ((isCompact_closedBall z0 δ).prod (isCompact_closedBall (0 : ℂ) R)).image
      (_root_.continuous_update (i := j))
  obtain ⟨M1, hM1⟩ := hKcomp.exists_bound_of_continuousOn hη.continuousOn
  have hKne : K.Nonempty := by
    refine ⟨Function.update z0 j 0, ⟨(z0, 0), ⟨?_, ?_⟩, rfl⟩⟩
    · simpa using hδpos.le
    · simpa using hR0.le
  obtain ⟨x0, hx0⟩ := hKne
  have hM1nn : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 x0 hx0)
  -- the uniform bound on the integrand near `z0`
  set M : ℝ := M1 * (s j - r j)⁻¹ ^ (l + 1) with hMdef
  set F : (Fin n → ℂ) → ℂ → ℂ :=
    fun z w => η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1) with hFdef
  have hAmeas : MeasurableSet (Work.NN.Core.fiberAnnulus (s j) R) :=
    Work.NN.Core.measurableSet_fiberAnnulus (s j) R
  -- pointwise convergence of the integrands, for almost every `w`
  have hlim : ∀ᵐ w ∂((volume : Measure ℂ).restrict (Work.NN.Core.fiberAnnulus (s j) R)),
      Tendsto (fun z => F z w) (𝓝 z0) (𝓝 (F z0 w)) := by
    filter_upwards [self_mem_ae_restrict hAmeas] with w hw
    have hz0j : ‖z0 j‖ < r j := by simpa using hz0 j
    have hwne : w ≠ z0 j := by
      intro h
      have hle : s j ≤ ‖z0 j‖ := h ▸ hw.1
      linarith [hle, le_of_lt hz0j, hrs j]
    have hne : w - z0 j ≠ 0 := sub_ne_zero.mpr hwne
    have hupd : Continuous fun z : Fin n → ℂ => Function.update z j w :=
      (_root_.continuous_update (i := j)).comp (continuous_id.prodMk continuous_const)
    have hker : ContinuousAt (fun z : Fin n → ℂ => ((w - z j)⁻¹) ^ (l + 1)) z0 :=
      (((continuous_const.sub (continuous_apply j)).continuousAt).inv₀ hne).pow (l + 1)
    rw [hFdef]
    exact (hη.continuousAt.comp hupd.continuousAt).mul hker
  have hFmeas : ∀ᶠ z in 𝓝 z0, AEStronglyMeasurable (F z)
      ((volume : Measure ℂ).restrict (Work.NN.Core.fiberAnnulus (s j) R)) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [hFdef]
    exact ((hη.measurable.comp (continuous_update z j).measurable).mul
      (((measurable_id.sub_const (z j)).inv).pow_const (l + 1))).aestronglyMeasurable
  -- the dominating function
  have hbound : ∀ᶠ z in 𝓝 z0,
      ∀ᵐ w ∂((volume : Measure ℂ).restrict (Work.NN.Core.fiberAnnulus (s j) R)),
      ‖F z w‖ ≤ (fun _ : ℂ => M) w := by
    filter_upwards [Metric.ball_mem_nhds z0 hδpos] with z hz
    have hzmem : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r := hδsub hz
    filter_upwards [self_mem_ae_restrict hAmeas] with w hw
    have hzj : ‖z j‖ < r j := by simpa using hzmem j
    have hKz : ‖((w - z j)⁻¹) ^ (l + 1)‖ ≤ (s j - r j)⁻¹ ^ (l + 1) :=
      Work.NN.Core.norm_pow_inv_le_of_mem_fiberAnnulus (s := s j) (R := R) hd l hw
        (by linarith [le_of_lt hzj])
    have hAle : ‖η (Function.update z j w)‖ ≤ M1 := by
      refine hM1 _ ⟨(z, w), ⟨?_, ?_⟩, rfl⟩
      · simpa using (Metric.mem_ball.mp hz).le
      · simpa using hw.2.le
    rw [hFdef, norm_mul, hMdef]
    exact mul_le_mul hAle hKz (norm_nonneg _) hM1nn
  have hboundint : Integrable (fun _ : ℂ => M)
      ((volume : Measure ℂ).restrict (Work.NN.Core.fiberAnnulus (s j) R)) :=
    integrableOn_const (C := M) (Work.NN.Core.volume_fiberAnnulus_lt_top (s j) R).ne (by simp)
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℂ).restrict (Work.NN.Core.fiberAnnulus (s j) R))
    (l := 𝓝 z0) (F := F) (f := F z0) (fun _ : ℂ => M) hFmeas hbound hboundint hlim
  have hscaled := hmain.const_mul (-((Real.pi : ℂ))⁻¹)
  have hfp : (fun z => Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η z)
      = fun z => -((Real.pi : ℂ))⁻¹ * ∫ w, F z w
          ∂((volume : Measure ℂ).restrict (Work.NN.Core.fiberAnnulus (s j) R)) := by
    funext z
    rw [hFdef, Work.NN.Core.fiberPotAnn_apply]
  have hcontAt : ContinuousAt
      (fun z => Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η z) z0 := by
    rw [hfp]
    exact hscaled
  exact hcontAt.continuousWithinAt

end Work.NN.Core

end
