import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# Differentiation under the integral sign for the regularized Cauchy transform

For `ω : ℂ → ℂ` of class `C²` with compact support, the regularized Cauchy transform `cauchyT ω`
is real-differentiable at every point `z`, with derivative `-(1/π) • ∫ η, dIntegrand ω z η`.

The proof is the parametric integral theorem `hasFDerivAt_integral_of_dominated_of_fderiv_le`:
the regularization `(ω (z+η) - ω z · cut η)/η` has a bounded, compactly supported derivative
integrand (the cutoff removes the singularity at `η = 0`), so a constant multiple of an indicator
of a large ball is an integrable dominating function.
-/

open MeasureTheory
open scoped Topology

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- The pointwise derivative of the Cauchy integrand. -/
private lemma hasFDerivAt_cauchyIntegrand (ω : ℂ → ℂ) (hω : Differentiable ℝ ω) (z' η : ℂ) :
    HasFDerivAt (fun z'' : ℂ => (ω (z'' + η) - ω z'' * cutC η) / η) (dIntegrand ω z' η) z' := by
  have hid : HasFDerivAt (fun z'' : ℂ => z'' + η) (ContinuousLinearMap.id ℝ ℂ) z' :=
    (hasFDerivAt_id z').add_const η
  have key : (fun z'' : ℂ => ω (z'' + η)) = (ω ∘ fun z'' : ℂ => z'' + η) := rfl
  have h1 : HasFDerivAt (fun z'' : ℂ => ω (z'' + η)) (fderiv ℝ ω (z' + η)) z' := by
    rw [key]
    simpa using (hω (z' + η)).hasFDerivAt.comp z' hid
  have h2 : HasFDerivAt (fun z'' : ℂ => ω z'' * cutC η) ((cutC η) • fderiv ℝ ω z') z' :=
    (hω z').hasFDerivAt.mul_const (cutC η)
  have h3 : HasFDerivAt ((fun z'' : ℂ => ω (z'' + η)) - fun z'' : ℂ => ω z'' * cutC η)
      ((fderiv ℝ ω (z' + η)) - (cutC η) • fderiv ℝ ω z') z' := h1.sub h2
  have h4 := h3.mul_const η⁻¹
  have key2 : ((fun z'' : ℂ => ω (z'' + η)) - fun z'' : ℂ => ω z'' * cutC η)
      = fun z'' : ℂ => ω (z'' + η) - ω z'' * cutC η := by
    funext z''; simp [Pi.sub_apply]
  have hfun : (fun z'' : ℂ => (ω (z'' + η) - ω z'' * cutC η) / η)
      = (fun z'' : ℂ => (ω (z'' + η) - ω z'' * cutC η) * η⁻¹) := by
    funext z''; rw [div_eq_mul_inv]
  rw [key2] at h4
  rw [show dIntegrand ω z' η = η⁻¹ • ((fderiv ℝ ω (z' + η)) - (cutC η) • fderiv ℝ ω z')
      from rfl, hfun]
  exact h4

/-- **Differentiation under the integral sign for `cauchyT`.**  For `ω` of class `C²` with compact
support, `cauchyT ω` is real-differentiable at every point with derivative `-(1/π)` times the
integral of `dIntegrand`. -/
theorem hasFDerivAt_cauchyT (ω : ℂ → ℂ) (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    HasFDerivAt (cauchyT ω) ((-((Real.pi : ℂ)⁻¹)) • ∫ η, dIntegrand ω z η) z := by
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hRsub : tsupport ω ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hRzero : ∀ w : ℂ, R < ‖w‖ → ω w = 0 := fun w hw =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have h := hRsub hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact absurd h (not_le_of_gt hw)
  have hd0 : ∀ w : ℂ, w ∉ tsupport ω → fderiv ℝ ω w = 0 := by
    intro w hw
    have hev : ω =ᶠ[𝓝 w] 0 := by
      filter_upwards [(isClosed_tsupport ω).isOpen_compl.mem_nhds hw] with u hu
      exact image_eq_zero_of_notMem_tsupport hu
    rw [hev.fderiv_eq]; simp
  have hDω : ContDiff ℝ 1 fun w : ℂ => fderiv ℝ ω w :=
    (contDiff_succ_iff_fderiv.mp hω).2.2
  have hdcont : Continuous fun w : ℂ => fderiv ℝ ω w := hDω.continuous
  have hddcont : Continuous fun w : ℂ => fderiv ℝ (fun u : ℂ => fderiv ℝ ω u) w :=
    hDω.continuous_fderiv one_ne_zero
  -- global bounds
  obtain ⟨M₀, hM₀nonneg, hM₀⟩ := exists_bound_of_cont_of_support hω.continuous hc
    (fun w hw => image_eq_zero_of_notMem_tsupport hw)
  obtain ⟨M₁, hM₁nonneg, hM₁⟩ := exists_bound_of_cont_of_support hdcont hc hd0
  obtain ⟨M₂, hM₂nonneg, hM₂⟩ := exists_bound_of_cont_of_support
    (f := fun w : ℂ => fderiv ℝ (fun u : ℂ => fderiv ℝ ω u) w) hddcont hc
    (fun w hw => by
      have hev : (fun u : ℂ => fderiv ℝ ω u) =ᶠ[𝓝 w] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport ω).isOpen_compl.mem_nhds hw] with u hu
        exact hd0 u hu
      rw [hev.fderiv_eq]; simp)
  -- Lipschitz bounds
  have hLip : ∀ w w' : ℂ, ‖fderiv ℝ ω w' - fderiv ℝ ω w‖ ≤ M₂ * ‖w' - w‖ := by
    intro w w'
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fun u : ℂ => fderiv ℝ ω u) (C := M₂) (s := Set.univ)
      (fun u _ => hDω.differentiable one_ne_zero u) (fun u _ => hM₂ u) convex_univ
      (Set.mem_univ w) (Set.mem_univ w')
    simpa using h
  have hωLip : ∀ w w' : ℂ, ‖ω w - ω w'‖ ≤ M₁ * ‖w - w'‖ := by
    intro w w'
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := ω) (C := M₁) (s := Set.univ)
      (fun u _ => (hω.of_le (by norm_num)).differentiable one_ne_zero u) (fun u _ => hM₁ u)
      convex_univ (Set.mem_univ w') (Set.mem_univ w)
    simpa using h
  -- strong measurability
  have haesF : ∀ z' : ℂ,
      AEStronglyMeasurable (fun η : ℂ => (ω (z' + η) - ω z' * cutC η) / η) volume := by
    intro z'
    have h1 : Measurable fun η : ℂ => ω (z' + η) :=
      hω.continuous.measurable.comp (by fun_prop)
    have h2 : Measurable fun η : ℂ => ω z' * cutC η :=
      measurable_const.mul contDiff_cutC.continuous.measurable
    exact ((h1.sub h2).div measurable_id).aestronglyMeasurable
  have haesF' : AEStronglyMeasurable (dIntegrand ω z) volume := by
    have hf : Measurable fun η : ℂ => fderiv ℝ ω (z + η) :=
      hdcont.measurable.comp (by fun_prop)
    have hc' : Measurable fun η : ℂ => cutC η := contDiff_cutC.continuous.measurable
    have h2 : Measurable fun η : ℂ => (cutC η) • fderiv ℝ ω z := hc'.smul measurable_const
    have h3 : Measurable fun η : ℂ => η⁻¹ := measurable_inv
    have h4 : Measurable fun η : ℂ =>
        η⁻¹ • ((fderiv ℝ ω (z + η)) - (cutC η) • fderiv ℝ ω z) :=
      h3.smul (hf.sub h2)
    have h5 : (fun η : ℂ => η⁻¹ • ((fderiv ℝ ω (z + η)) - (cutC η) • fderiv ℝ ω z))
        = dIntegrand ω z := by
      funext η; rfl
    rw [← h5]
    exact h4.aestronglyMeasurable
  -- integrability of the integrand at `z`
  have hmaj1 : Integrable (fun η : ℂ => max M₁ (4 * M₀) *
      (Metric.closedBall 0 (max (R + ‖z‖) 1)).indicator (fun _ => (1 : ℝ)) η) volume := by
    refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff (isCompact_closedBall (0 : ℂ) (max (R + ‖z‖) 1)).measurableSet]
    exact integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne (by simp)
  have hint : Integrable (fun η : ℂ => (ω (z + η) - ω z * cutC η) / η) volume := by
    refine Integrable.mono' hmaj1 (haesF z) ?_
    filter_upwards with η
    by_cases hη : ‖η‖ ≤ max (R + ‖z‖) 1
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hη), mul_one]
      by_cases h2 : ‖η‖ ≤ 1 / 2
      · rw [cutC_eq_one (by nlinarith [norm_nonneg η]), mul_one]
        by_cases hη0 : η = 0
        · rw [hη0, div_zero, norm_zero]
          positivity
        · have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
          have h3 : ‖ω (z + η) - ω z‖ ≤ M₁ * ‖η‖ := by
            have h4 := hωLip (z + η) z
            rwa [add_sub_cancel_left] at h4
          calc ‖(ω (z + η) - ω z) / η‖ = ‖ω (z + η) - ω z‖ * ‖η‖⁻¹ := by
                rw [div_eq_mul_inv, norm_mul, norm_inv]
            _ ≤ (M₁ * ‖η‖) * ‖η‖⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
            _ = M₁ := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
            _ ≤ max M₁ (4 * M₀) := le_max_left _ _
      · have h3 : ‖ω (z + η)‖ ≤ M₀ := hM₀ _
        have h5 : ‖η‖⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith [not_le.mp h2]) (by norm_num)]
          linarith [not_le.mp h2]
        calc ‖(ω (z + η) - ω z * cutC η) / η‖
            = ‖ω (z + η) - ω z * cutC η‖ * ‖η‖⁻¹ := by rw [div_eq_mul_inv, norm_mul, norm_inv]
          _ ≤ (M₀ + M₀) * 2 := by
              refine mul_le_mul ?_ h5 (by positivity) (by positivity)
              calc ‖ω (z + η) - ω z * cutC η‖ ≤ ‖ω (z + η)‖ + ‖ω z * cutC η‖ := norm_sub_le _ _
                _ ≤ M₀ + M₀ := by
                    refine add_le_add h3 ?_
                    rw [norm_mul]
                    calc ‖ω z‖ * ‖cutC η‖ ≤ M₀ * 1 :=
                          mul_le_mul (hM₀ z) (norm_cutC_le_one η) (norm_nonneg _) hM₀nonneg
                      _ = M₀ := by ring
          _ ≤ max M₁ (4 * M₀) := by
              have : (M₀ + M₀) * 2 = 4 * M₀ := by ring
              rw [this]; exact le_max_right _ _
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using hη),
        mul_zero]
      have hRlt : R < ‖η‖ - ‖z‖ := by
        have h5 : max (R + ‖z‖) 1 < ‖η‖ := not_le.mp hη
        linarith [le_max_left (R + ‖z‖) 1]
      have hbig : R < ‖z + η‖ := by
        have h3 : ‖η‖ - ‖z‖ ≤ ‖z + η‖ := by
          have h := abs_norm_sub_norm_le η (-z)
          have h2 := le_abs_self (‖η‖ - ‖-z‖)
          rw [show η - -z = z + η by ring] at h
          simp only [norm_neg] at h h2
          linarith
        linarith
      have h1 : ω (z + η) = 0 := hRzero _ hbig
      have h6 : cutC η = 0 := by
        have h7 : (1 : ℝ) < ‖η‖ := by
          have h5 : max (R + ‖z‖) 1 < ‖η‖ := not_le.mp hη
          linarith [le_max_right (R + ‖z‖) 1]
        have h8 : 3 / 4 ≤ ‖η‖ ^ 2 := by nlinarith [norm_nonneg η]
        rw [cutC, cut_eq_zero h8]
        simp
      rw [h1, h6, mul_zero, sub_zero, zero_div]
      simp
  -- integrability of the dominating function for the derivative, and the domination
  have hmaj2 : Integrable (fun η : ℂ => (M₂ + 2 * M₁) *
      (Metric.closedBall 0 (max (R + ‖z‖ + 1) 2)).indicator (fun _ => (1 : ℝ)) η) volume := by
    refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff (isCompact_closedBall (0 : ℂ) (max (R + ‖z‖ + 1) 2)).measurableSet]
    exact integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne (by simp)
  have hdom : ∀ z' ∈ Metric.ball z 1, ∀ η : ℂ, ‖dIntegrand ω z' η‖ ≤ (M₂ + 2 * M₁) *
      (Metric.closedBall 0 (max (R + ‖z‖ + 1) 2)).indicator (fun _ => (1 : ℝ)) η := by
    intro z' hz' η
    by_cases hη : ‖η‖ ≤ max (R + ‖z‖ + 1) 2
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hη), mul_one]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
      rw [dIntegrand_apply]
      by_cases hη0 : η = 0
      · rw [hη0, inv_zero, zero_mul, norm_zero]
        positivity
      · have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
        have hA : ‖(fderiv ℝ ω z') h‖ ≤ M₁ * ‖h‖ := by
          calc ‖(fderiv ℝ ω z') h‖ ≤ ‖fderiv ℝ ω z'‖ * ‖h‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ M₁ * ‖h‖ := mul_le_mul_of_nonneg_right (hM₁ _) (norm_nonneg _)
        have hAB : ‖(fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h‖ ≤ M₂ * ‖η‖ * ‖h‖ := by
          calc ‖(fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h‖
              ≤ ‖fderiv ℝ ω (z' + η) - fderiv ℝ ω z'‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (M₂ * ‖η‖) * ‖h‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                have h4 := hLip z' (z' + η)
                rw [add_sub_cancel_left] at h4
                exact h4
        have hdecomp : (fderiv ℝ ω (z' + η)) h - cutC η * (fderiv ℝ ω z') h
            = (fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h + (fderiv ℝ ω z') h * (1 - cutC η) := by
          rw [ContinuousLinearMap.sub_apply]; ring
        rw [hdecomp, norm_mul, norm_inv, mul_comm]
        have hbd : ‖(fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h
            + (fderiv ℝ ω z') h * (1 - cutC η)‖ ≤ (M₂ + 2 * M₁) * ‖η‖ * ‖h‖ := by
          calc ‖(fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h
                + (fderiv ℝ ω z') h * (1 - cutC η)‖
              ≤ ‖(fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h‖
                + ‖(fderiv ℝ ω z') h * (1 - cutC η)‖ := norm_add_le _ _
            _ ≤ M₂ * ‖η‖ * ‖h‖ + (M₁ * ‖h‖) * (2 * ‖η‖) := by
                refine add_le_add hAB ?_
                rw [norm_mul]
                exact mul_le_mul hA (norm_one_sub_cutC_le η) (norm_nonneg _) (by positivity)
            _ = (M₂ + 2 * M₁) * ‖η‖ * ‖h‖ := by ring
        calc ‖(fderiv ℝ ω (z' + η) - fderiv ℝ ω z') h + (fderiv ℝ ω z') h * (1 - cutC η)‖
              * ‖η‖⁻¹
            ≤ ((M₂ + 2 * M₁) * ‖η‖ * ‖h‖) * ‖η‖⁻¹ :=
              mul_le_mul_of_nonneg_right hbd (by positivity)
          _ = (M₂ + 2 * M₁) * ‖h‖ := by
              field_simp
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using hη),
        mul_zero]
      have hzero : dIntegrand ω z' η = 0 := by
        have hbig : R < ‖z' + η‖ := by
          have h5 : max (R + ‖z‖ + 1) 2 < ‖η‖ := not_le.mp hη
          have hz'le : ‖z' - z‖ < 1 := by
            have := hz'
            simpa [Metric.mem_ball, dist_eq_norm] using this
          have h3 : ‖η‖ - ‖z'‖ ≤ ‖z' + η‖ := by
            have h := abs_norm_sub_norm_le η (-z')
            have h2 := le_abs_self (‖η‖ - ‖-z'‖)
            rw [show η - -z' = z' + η by ring] at h
            simp only [norm_neg] at h h2
            linarith
          have h4 : ‖z'‖ ≤ 1 + ‖z‖ := by
            calc ‖z'‖ = ‖(z' - z) + z‖ := by rw [sub_add_cancel]
              _ ≤ ‖z' - z‖ + ‖z‖ := norm_add_le _ _
              _ ≤ 1 + ‖z‖ := by linarith [hz'le]
          have h6 : R + ‖z'‖ < ‖η‖ := by
            have h7 : R + ‖z‖ + 1 < ‖η‖ := lt_of_le_of_lt (le_max_left _ _) h5
            linarith
          linarith
        have h1 : fderiv ℝ ω (z' + η) = 0 := hd0 _ (fun hmem => by
          have h2 := hRsub hmem
          rw [Metric.mem_closedBall, dist_zero_right] at h2
          exact absurd h2 (not_le_of_gt hbig))
        have h6 : cutC η = 0 := by
          have h7 : (1 : ℝ) < ‖η‖ := by
            have h5 : max (R + ‖z‖ + 1) 2 < ‖η‖ := not_le.mp hη
            linarith [le_max_right (R + ‖z‖ + 1) 2]
          have h8 : 3 / 4 ≤ ‖η‖ ^ 2 := by nlinarith [norm_nonneg η]
          rw [cutC, cut_eq_zero h8]
          simp
        rw [dIntegrand, h1, h6]
        simp
      rw [hzero]; simp
  -- the parametric integral theorem
  have hmain : HasFDerivAt (fun z' : ℂ => ∫ η, (ω (z' + η) - ω z' * cutC η) / η)
      (∫ η, dIntegrand ω z η) z := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (𝕜 := ℝ)
      (s := Metric.ball z 1) (x₀ := z)
      (bound := fun η : ℂ => (M₂ + 2 * M₁) *
        (Metric.closedBall 0 (max (R + ‖z‖ + 1) 2)).indicator (fun _ => (1 : ℝ)) η)
      (F := fun z' η => (ω (z' + η) - ω z' * cutC η) / η)
      (F' := fun z' η => dIntegrand ω z' η)
      (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall fun z' => haesF z') hint haesF'
      (Filter.Eventually.of_forall fun η z' hz' => hdom z' hz' η) hmaj2
      (Filter.Eventually.of_forall fun η z' _ =>
        hasFDerivAt_cauchyIntegrand ω (hω.differentiable (by decide)) z' η)
  -- multiply by the constant `-(1/π)`
  have hsmul := hmain.const_smul (-((Real.pi : ℂ)⁻¹))
  have hfun : cauchyT ω = fun z' : ℂ =>
      -((Real.pi : ℂ)⁻¹) * ∫ η, (ω (z' + η) - ω z' * cutC η) / η := by
    funext z'; rfl
  rw [hfun]
  exact hsmul

end Work.Analysis.Complex.DbarCauchy

end
