import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped Convolution

/-- The `2`-`rpow` of the extended norm of a complex number equals the `ofReal` of the square
of its norm. -/
private lemma enorm_rpow_two_c (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm z]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  exact (ENNReal.ofReal_pow (norm_nonneg z) 2).symm

/-- The squared norm on `ℂ` is convex. -/
private lemma convexOn_univ_norm_sq_c : ConvexOn ℝ Set.univ (fun v : ℂ => ‖v‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  calc ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 := by gcongr
    _ ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
        nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg ha hb, hab, ha, hb]

theorem eLpNorm_convolution_compactSupport {ρ : ℂ → ℝ} {f : ℂ → ℂ} {M : ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρ1 : ∫ x, ρ x ∂MeasureTheory.volume = 1)
    (hf : Continuous f) (hfM : ∀ z, ‖f z‖ ≤ M) (hfs : HasCompactSupport f) :
    MeasureTheory.eLpNorm (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume) 2 MeasureTheory.volume
      ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.volume := by
  have hρmeas : Measurable ρ := hρc.measurable
  have hρdmeas : Measurable (fun y : ℂ => ENNReal.ofReal (ρ y)) := hρmeas.ennreal_ofReal
  have hρint : Integrable ρ MeasureTheory.volume := hρc.integrable_of_hasCompactSupport hρs
  -- the normalized measure `ρ · volume`
  have hρlin : ∫⁻ y, ENNReal.ofReal (ρ y) ∂MeasureTheory.volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρint (Filter.Eventually.of_forall hρ0), hρ1]
    simp
  -- pointwise Jensen bound
  have hpt : ∀ x, ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖f (x - y)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
    intro x
    let ν : Measure ℂ := MeasureTheory.volume.withDensity (fun y => ENNReal.ofReal (ρ y))
    have hν_univ : ν Set.univ = 1 := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hρlin
    haveI : IsProbabilityMeasure ν := ⟨hν_univ⟩
    have hf_cont : Continuous (fun y : ℂ => f (x - y)) :=
      hf.comp (continuous_const.sub continuous_id)
    have hfi : Integrable (fun y : ℂ => f (x - y)) ν :=
      Integrable.of_bound hf_cont.aestronglyMeasurable M
        (Filter.Eventually.of_forall (fun y => hfM _))
    have hgi : Integrable (fun y : ℂ => ‖f (x - y)‖ ^ 2) ν := by
      have hcont : Continuous (fun y : ℂ => ‖f (x - y)‖ ^ 2) := (hf_cont.norm).pow 2
      refine Integrable.of_bound hcont.aestronglyMeasurable (M ^ 2)
        (Filter.Eventually.of_forall (fun y => ?_))
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hfM _) 2
    have hjensen := ConvexOn.map_integral_le convexOn_univ_norm_sq_c
        (continuous_norm.pow 2).continuousOn isClosed_univ
        (Filter.Eventually.of_forall (fun y => Set.mem_univ _)) hfi hgi
    have hleft : ∫ y, f (x - y) ∂ν = MeasureTheory.convolution ρ f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
      rw [MeasureTheory.convolution_def]
      rw [integral_withDensity_eq_integral_toReal_smul hρdmeas
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun y => f (x - y))]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp only [ENNReal.toReal_ofReal (hρ0 y), ContinuousLinearMap.lsmul_apply]
    have hright : ENNReal.ofReal (∫ y, ‖f (x - y)‖ ^ 2 ∂ν)
        = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖f (x - y)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
      rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall (fun y => sq_nonneg _))]
      rw [show ν = MeasureTheory.volume.withDensity (fun y => ENNReal.ofReal (ρ y)) from rfl]
      rw [lintegral_withDensity_eq_lintegral_mul MeasureTheory.volume hρdmeas
        (show Measurable (fun a : ℂ => ENNReal.ofReal (‖f (x - a)‖ ^ 2)) from
          (hf_cont.norm.pow 2).measurable.ennreal_ofReal)]
      refine lintegral_congr (fun y => ?_)
      simp only [Pi.mul_apply, enorm_rpow_two_c]
    calc ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume x‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (‖∫ y, f (x - y) ∂ν‖ ^ 2) := by
          rw [← hleft]; exact enorm_rpow_two_c _
      _ ≤ ENNReal.ofReal (∫ y, ‖f (x - y)‖ ^ 2 ∂ν) := ENNReal.ofReal_le_ofReal hjensen
      _ = ∫⁻ y, ENNReal.ofReal (ρ y) * ‖f (x - y)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := hright
  -- measurability of the kernel, for Tonelli
  have hnormmeas : ∀ y : ℂ, Measurable (fun x : ℂ => ‖f (x - y)‖ₑ ^ (2 : ℝ)) := fun y =>
    ((hf.measurable.comp (measurable_id.sub measurable_const)).enorm).pow_const (2 : ℝ)
  have hFmeas : AEMeasurable
      (Function.uncurry (fun x y : ℂ => ENNReal.ofReal (ρ y) * ‖f (x - y)‖ₑ ^ (2 : ℝ)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine Measurable.aemeasurable ?_
    exact (hρdmeas.comp measurable_snd).mul
      (((hf.measurable.comp (measurable_fst.sub measurable_snd)).enorm).pow_const (2 : ℝ))
  -- main inequality on the `ℒ²` seminorms
  have hmain : (∫⁻ x, ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume)
      ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
    calc ∫⁻ x, ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ y) * ‖f (x - y)‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ∂MeasureTheory.volume := lintegral_mono hpt
      _ = ∫⁻ y, ENNReal.ofReal (ρ y) * (∫⁻ x, ‖f (x - y)‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume) ∂MeasureTheory.volume := by
          rw [lintegral_lintegral_swap hFmeas]
          refine lintegral_congr (fun y => ?_)
          rw [lintegral_const_mul _ (hnormmeas y)]
      _ = ∫⁻ y, ENNReal.ofReal (ρ y) * (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume) ∂MeasureTheory.volume := by
          refine lintegral_congr (fun y => ?_)
          rw [lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ (2 : ℝ)) y]
      _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
          rw [lintegral_mul_const _ hρdmeas, hρlin, one_mul]
  have hcont : Continuous (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
      MeasureTheory.volume) :=
    hρs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hf.locallyIntegrable
  have hAc : (∫⁻ x, ‖MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume)
      = MeasureTheory.eLpNorm (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume) 2 MeasureTheory.volume ^ (2 : ℝ) :=
    (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hcont.aestronglyMeasurable).symm
  have hBf : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume)
      = MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ (2 : ℝ) :=
    (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf.aestronglyMeasurable).symm
  have hsq : MeasureTheory.eLpNorm (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume) 2 MeasureTheory.volume ^ (2 : ℝ)
      ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.volume ^ (2 : ℝ) := by
    rw [← hAc, ← hBf]
    exact hmain
  exact (ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < 2 by norm_num)).mp hsq

end Work.Beltrami
