import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Work.Analysis.Complex.DbarCauchy.hasFDerivAt_cauchyT

/-!
# Smoothness of the regularized Cauchy transform

For `ω : ℂ → ℂ` of class `C^∞` with compact support, `cauchyT ω` is again of class `C^∞`.

The proof is a recursion: by `hasFDerivAt_cauchyT`, the Fréchet derivative of `cauchyT ω` at `x`,
evaluated at `y`, equals `cauchyT (fun w => fderiv ℝ ω w y) x`; since `ω ↦ fderiv ℝ ω · y` preserves
`C^∞`-with-compact-support, the induction closes.
-/

open MeasureTheory
open scoped Topology

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- A global bound for `dIntegrand`: for `ω` of class `C²` with compact support there is a constant
`C ≥ 0` with `‖dIntegrand ω z η‖ ≤ C` for all `z, η`. -/
theorem exists_bound_dIntegrand (ω : ℂ → ℂ) (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z η : ℂ, ‖dIntegrand ω z η‖ ≤ C := by
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hRsub : tsupport ω ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
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
  obtain ⟨M₁, hM₁nonneg, hM₁⟩ := exists_bound_of_cont_of_support hdcont hc hd0
  obtain ⟨M₂, hM₂nonneg, hM₂⟩ := exists_bound_of_cont_of_support
    (f := fun w : ℂ => fderiv ℝ (fun u : ℂ => fderiv ℝ ω u) w) hddcont hc
    (fun w hw => by
      have hev : (fun u : ℂ => fderiv ℝ ω u) =ᶠ[𝓝 w] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport ω).isOpen_compl.mem_nhds hw] with u hu
        exact hd0 u hu
      rw [hev.fderiv_eq]; simp)
  have hLip : ∀ w w' : ℂ, ‖fderiv ℝ ω w' - fderiv ℝ ω w‖ ≤ M₂ * ‖w' - w‖ := by
    intro w w'
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fun u : ℂ => fderiv ℝ ω u) (C := M₂) (s := Set.univ)
      (fun u _ => hDω.differentiable one_ne_zero u) (fun u _ => hM₂ u) convex_univ
      (Set.mem_univ w) (Set.mem_univ w')
    simpa using h
  refine ⟨M₂ + 2 * M₁, by positivity, fun z η => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [dIntegrand_apply]
  by_cases hη0 : η = 0
  · rw [hη0, inv_zero, zero_mul, norm_zero]
    positivity
  · have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
    have hA : ‖(fderiv ℝ ω z) h‖ ≤ M₁ * ‖h‖ := by
      calc ‖(fderiv ℝ ω z) h‖ ≤ ‖fderiv ℝ ω z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M₁ * ‖h‖ := mul_le_mul_of_nonneg_right (hM₁ _) (norm_nonneg _)
    have hAB : ‖(fderiv ℝ ω (z + η) - fderiv ℝ ω z) h‖ ≤ M₂ * ‖η‖ * ‖h‖ := by
      calc ‖(fderiv ℝ ω (z + η) - fderiv ℝ ω z) h‖
          ≤ ‖fderiv ℝ ω (z + η) - fderiv ℝ ω z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (M₂ * ‖η‖) * ‖h‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have h4 := hLip z (z + η)
            rw [add_sub_cancel_left] at h4
            exact h4
    have hdecomp : fderiv ℝ ω (z + η) h - cutC η * fderiv ℝ ω z h
        = (fderiv ℝ ω (z + η) - fderiv ℝ ω z) h + fderiv ℝ ω z h * (1 - cutC η) := by
      rw [ContinuousLinearMap.sub_apply]; ring
    rw [hdecomp, norm_mul, norm_inv, mul_comm]
    have hbd : ‖(fderiv ℝ ω (z + η) - fderiv ℝ ω z) h + fderiv ℝ ω z h * (1 - cutC η)‖
        ≤ (M₂ + 2 * M₁) * ‖η‖ * ‖h‖ := by
      calc ‖(fderiv ℝ ω (z + η) - fderiv ℝ ω z) h + fderiv ℝ ω z h * (1 - cutC η)‖
          ≤ ‖(fderiv ℝ ω (z + η) - fderiv ℝ ω z) h‖ + ‖fderiv ℝ ω z h * (1 - cutC η)‖ :=
            norm_add_le _ _
        _ ≤ M₂ * ‖η‖ * ‖h‖ + (M₁ * ‖h‖) * (2 * ‖η‖) := by
            refine add_le_add hAB ?_
            rw [norm_mul]
            exact mul_le_mul hA (norm_one_sub_cutC_le η) (norm_nonneg _) (by positivity)
        _ = (M₂ + 2 * M₁) * ‖η‖ * ‖h‖ := by ring
    calc ‖(fderiv ℝ ω (z + η) - fderiv ℝ ω z) h + fderiv ℝ ω z h * (1 - cutC η)‖ * ‖η‖⁻¹
        ≤ ((M₂ + 2 * M₁) * ‖η‖ * ‖h‖) * ‖η‖⁻¹ :=
          mul_le_mul_of_nonneg_right hbd (by positivity)
      _ = (M₂ + 2 * M₁) * ‖h‖ := by field_simp

/-- `dIntegrand ω z` is strongly measurable. -/
theorem aestronglyMeasurable_dIntegrand (ω : ℂ → ℂ) (hω : ContDiff ℝ 1 ω) (z : ℂ) :
    AEStronglyMeasurable (dIntegrand ω z) volume := by
  have hdcont : Continuous fun w : ℂ => fderiv ℝ ω w := hω.continuous_fderiv one_ne_zero
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

/-- `dIntegrand ω z` is integrable, being bounded and compactly supported. -/
theorem integrable_dIntegrand (ω : ℂ → ℂ) (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    Integrable (dIntegrand ω z) volume := by
  obtain ⟨C, hCnonneg, hC⟩ := exists_bound_dIntegrand ω hω hc
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hRsub : tsupport ω ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hd0 : ∀ w : ℂ, w ∉ tsupport ω → fderiv ℝ ω w = 0 := by
    intro w hw
    have hev : ω =ᶠ[𝓝 w] 0 := by
      filter_upwards [(isClosed_tsupport ω).isOpen_compl.mem_nhds hw] with u hu
      exact image_eq_zero_of_notMem_tsupport hu
    rw [hev.fderiv_eq]; simp
  have hzero : ∀ η : ℂ, max (R + ‖z‖ + 1) 2 < ‖η‖ → dIntegrand ω z η = 0 := by
    intro η hη
    have hbig : R < ‖z + η‖ := by
      have h5 : max (R + ‖z‖ + 1) 2 < ‖η‖ := hη
      have h3 : ‖η‖ - ‖z‖ ≤ ‖z + η‖ := by
        have h := abs_norm_sub_norm_le η (-z)
        have h2 := le_abs_self (‖η‖ - ‖-z‖)
        rw [show η - -z = z + η by ring] at h
        simp only [norm_neg] at h h2
        linarith
      have h6 : R + ‖z‖ + 1 < ‖η‖ := lt_of_le_of_lt (le_max_left _ _) h5
      linarith
    have h1 : fderiv ℝ ω (z + η) = 0 := hd0 _ (fun hmem => by
      have h2 := hRsub hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      exact absurd h2 (not_le_of_gt hbig))
    have h6 : cutC η = 0 := by
      have h7 : (1 : ℝ) < ‖η‖ := by
        have h5 : max (R + ‖z‖ + 1) 2 < ‖η‖ := hη
        linarith [le_max_right (R + ‖z‖ + 1) 2]
      have h8 : 3 / 4 ≤ ‖η‖ ^ 2 := by nlinarith [norm_nonneg η]
      rw [cutC, cut_eq_zero h8]
      simp
    rw [dIntegrand, h1, h6]
    simp
  have hmaj : Integrable (fun η : ℂ => C *
      (Metric.closedBall 0 (max (R + ‖z‖ + 1) 2)).indicator (fun _ => (1 : ℝ)) η) volume := by
    refine Integrable.const_mul ?_ C
    rw [integrable_indicator_iff (isCompact_closedBall (0 : ℂ) (max (R + ‖z‖ + 1) 2)).measurableSet]
    exact integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne (by simp)
  refine Integrable.mono' hmaj (aestronglyMeasurable_dIntegrand ω (hω.of_le (by norm_num)) z) ?_
  · filter_upwards with η
    by_cases hη : ‖η‖ ≤ max (R + ‖z‖ + 1) 2
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hη), mul_one]
      exact hC z η
    · rw [Set.indicator_of_notMem (by simpa [Metric.mem_closedBall, dist_zero_right] using hη),
        mul_zero, hzero η (not_le.mp hη), norm_zero]

/-- **The Fréchet derivative of `cauchyT` in continuous-linear-map form.**  The derivative of
`cauchyT ω` at `x`, evaluated at `y`, is the Cauchy transform of the directional derivative
`w ↦ fderiv ℝ ω w y`. -/
theorem fderiv_cauchyT_apply (ω : ℂ → ℂ) (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (x y : ℂ) : (fderiv ℝ (cauchyT ω) x) y = cauchyT (fun w => fderiv ℝ ω w y) x := by
  have hfd := hasFDerivAt_cauchyT ω hω hc x
  rw [hfd.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.integral_apply (integrable_dIntegrand ω hω hc x)]
  have hfun : cauchyT (fun w : ℂ => fderiv ℝ ω w y) x
      = -((Real.pi : ℂ)⁻¹) * ∫ η, (dIntegrand ω x η) y := by
    simp only [cauchyT]
    congr 1
    apply integral_congr_ae
    filter_upwards with η
    rw [dIntegrand_apply]
    simp only [div_eq_mul_inv]
    ring
  rw [hfun]

/-- **Smoothness of the regularized Cauchy transform.**  For `ω` of class `C^∞` with compact
support, `cauchyT ω` is of class `C^∞`. -/
theorem contDiff_cauchyT_nat (n : ℕ) (ω : ℂ → ℂ) (hω : ContDiff ℝ cinf ω)
    (hc : HasCompactSupport ω) : ContDiff ℝ n (cauchyT ω) := by
  induction n generalizing ω with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasFDerivAt_cauchyT ω (hω.of_le (natCast_le_cinf 2)) hc x).continuousAt
  | succ n ih =>
    rw [Nat.cast_add_one, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_cauchyT ω (hω.of_le (natCast_le_cinf 2)) hc x).differentiableAt,
      ?_, ?_⟩
    · intro h
      exact absurd h (WithTop.coe_ne_top)
    · intro y
      have hdir : (fun x : ℂ => fderiv ℝ (cauchyT ω) x y)
          = cauchyT (fun w => fderiv ℝ ω w y) := by
        funext x
        exact fderiv_cauchyT_apply ω (hω.of_le (natCast_le_cinf 2)) hc x y
      rw [hdir]
      refine ih (fun w => fderiv ℝ ω w y) ?_ ?_
      · have h1 : ContDiff ℝ cinf (fun w : ℂ => fderiv ℝ ω w) :=
          (contDiff_infty_iff_fderiv.mp hω).2
        exact ContDiff.comp
          (ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℂ y)) h1
      · refine HasCompactSupport.of_support_subset_isCompact hc ?_
        intro w hw
        rw [Function.mem_support] at hw
        by_contra hw'
        refine hw ?_
        have hev : ω =ᶠ[𝓝 w] 0 := by
          filter_upwards [(isClosed_tsupport ω).isOpen_compl.mem_nhds hw'] with u hu
          exact image_eq_zero_of_notMem_tsupport hu
        rw [hev.fderiv_eq]
        simp

/-- **Smoothness of the regularized Cauchy transform.** -/
theorem contDiff_cauchyT (ω : ℂ → ℂ) (hω : ContDiff ℝ cinf ω) (hc : HasCompactSupport ω) :
    ContDiff ℝ cinf (cauchyT ω) := by
  rw [contDiff_iff_forall_nat_le]
  intro n _
  exact contDiff_cauchyT_nat n ω hω hc

end Work.Analysis.Complex.DbarCauchy

end
