import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.dbarW_cauchyT_defs
import Submission.Work.Beltrami.tendsto_cutK_mul
import Submission.Work.Beltrami.tendsto_cutProfile_deriv
import Submission.Work.Beltrami.integrable_mul_cutK
import Submission.Work.Beltrami.contDiff_cutK_smooth
import Submission.Work.Beltrami.hasFDerivAt_cauchyInt_smooth

noncomputable section
namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

/-! ## The Pompeiu formula -/

/-- **Pompeiu formula.**  For a `C¹` compactly supported `f` and every `z`,
`∫ u, ∂̄f(z+u)/u = -π f(z)`. -/
theorem pompeiu (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (z : ℂ) :
    ∫ u, dbarW f (z + u) * u⁻¹ ∂volume = -(Real.pi : ℂ) * f z := by
  set F : ℂ → ℂ := fun u => f (z + u) with hFdef
  have hFcd : ContDiff ℝ 1 F := by
    rw [hFdef]; exact hf.comp (contDiff_const.add contDiff_id)
  have hFc : HasCompactSupport F := by
    rw [hFdef]
    have h := hc.comp_homeomorph (Homeomorph.addLeft z)
    convert h using 1
    ext u; simp
  have hkey : ∀ ε : ℝ, 0 < ε →
      ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) ∂volume
        = -∫ u, dbarW F u * cutK ε u ∂volume := by
    intro ε hε
    have hFcont : Continuous F := hFcd.continuous
    have hg1cont : Continuous (fun u => (fderiv ℝ F u) 1) :=
      (hFcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hg1c : HasCompactSupport (fun u => (fderiv ℝ F u) 1) :=
      (hFc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
    have hgIcont : Continuous (fun u => (fderiv ℝ F u) Complex.I) :=
      (hFcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hgIc : HasCompactSupport (fun u => (fderiv ℝ F u) Complex.I) :=
      (hFc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (by simp)
    have hck : ContDiff ℝ 1 (cutK ε) := contDiff_cutK_smooth ε
    have hck1cont : Continuous (fun u => (fderiv ℝ (cutK ε) u) 1) :=
      (hck.continuous_fderiv (by simp)).clm_apply continuous_const
    have hckIcont : Continuous (fun u => (fderiv ℝ (cutK ε) u) Complex.I) :=
      (hck.continuous_fderiv (by simp)).clm_apply continuous_const
    have hFG : Integrable (fun u => F u * cutK ε u) volume :=
      integrable_mul_cutK hFcont hFc ε
    have hF1 : Integrable (fun u => (fderiv ℝ F u 1) * cutK ε u) volume :=
      integrable_mul_cutK hg1cont hg1c ε
    have hFI : Integrable (fun u => (fderiv ℝ F u Complex.I) * cutK ε u) volume :=
      integrable_mul_cutK hgIcont hgIc ε
    have h1G : Integrable (fun u => F u * (fderiv ℝ (cutK ε) u 1)) volume :=
      (hFcont.mul hck1cont).integrable_of_hasCompactSupport hFc.mul_right
    have hIG : Integrable (fun u => F u * (fderiv ℝ (cutK ε) u Complex.I)) volume :=
      (hFcont.mul hckIcont).integrable_of_hasCompactSupport hFc.mul_right
    have hFd : ∀ u ∈ tsupport (cutK ε), DifferentiableAt ℝ F u :=
      fun u _ => (hFcd.differentiable (by simp)) u
    have hGd : ∀ u ∈ tsupport F, DifferentiableAt ℝ (cutK ε) u :=
      fun u _ => (hck.differentiable (by simp)) u
    have hIBP := integral_mul_dbarW_eq_neg F (cutK ε) hFG hF1 hFI h1G hIG hFd hGd
    rw [← hIBP]
    apply integral_congr_ae
    filter_upwards with u
    rw [dbarW_cutK ε hε u]
  have hlim1 : Filter.Tendsto
      (fun ε : ℝ => ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.pi : ℂ) * F 0)) :=
    tendsto_cutProfile_deriv F hFcd.continuous hFc
  have hdFcont : Continuous (dbarW F) := by
    have h : Continuous (fderiv ℝ F) := hFcd.continuous_fderiv (by simp)
    have h1 : Continuous (fun u => (fderiv ℝ F u) 1) := h.clm_apply continuous_const
    have hI : Continuous (fun u => (fderiv ℝ F u) Complex.I) := h.clm_apply continuous_const
    unfold dbarW dzbarCoeff
    exact (h1.add (continuous_const.mul hI)).div_const 2
  have hdFc : HasCompactSupport (dbarW F) := by
    have h := (hFc.fderiv ℝ).comp_left
      (g := fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I)/2) (by simp)
    unfold dbarW dzbarCoeff
    exact h
  have hlim2 : Filter.Tendsto
      (fun ε : ℝ => -∫ u, dbarW F u * cutK ε u ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-∫ u, dbarW F u * u⁻¹ ∂volume)) :=
    (tendsto_cutK_mul (dbarW F) hdFcont hdFc).neg
  have heq : (fun ε : ℝ => ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) ∂volume)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun ε : ℝ => -∫ u, dbarW F u * cutK ε u ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hkey ε hε
  have huniq : (Real.pi : ℂ) * F 0 = -∫ u, dbarW F u * u⁻¹ ∂volume :=
    tendsto_nhds_unique hlim1 (hlim2.congr' heq.symm)
  have hcong : ∫ u, dbarW F u * u⁻¹ ∂volume
      = ∫ u, dbarW f (z + u) * u⁻¹ ∂volume := by
    apply integral_congr_ae
    filter_upwards with u
    have huf : fderiv ℝ F u = fderiv ℝ f (z + u) := by
      rw [hFdef]; exact fderiv_comp_add_left z
    simp only [dbarW, dzbarCoeff, huf]
  have hF0 : F 0 = f z := by rw [hFdef]; simp
  rw [hcong, hF0] at huniq
  rw [neg_mul, huniq]
  ring


/-! ## Main theorem -/

/-- **Pompeiu formula for the Cauchy transform.** -/
theorem dbarW_cauchyT (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∀ z, dbarW (cauchyT f) z = f z := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  intro z
  set c : ℂ := ((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) with hc_def
  have hloc : LocallyIntegrable (fun u : ℂ => u⁻¹) (volume : Measure ℂ) := by
    refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (C := 1) (α := 1)
      ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · filter_upwards with x; rw [one_mul, norm_inv, Real.rpow_neg_one]
    · exact measurable_inv.aestronglyMeasurable
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    (hf1.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  have hfdmeas : Measurable (fun u : ℂ => fderiv ℝ f (z + u)) :=
    ((hf1.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).measurable
  set K : Set ℂ := (fun w : ℂ => w - z) '' tsupport f with hKdef
  have hK : IsCompact K := hc.isCompact.image (continuous_id.sub continuous_const)
  have hInt : Integrable (fun u => (u⁻¹ : ℂ) • fderiv ℝ f (z + u)) volume := by
    have hIK : Integrable (K.indicator (fun u => u⁻¹)) volume :=
      (integrable_indicator_iff hK.measurableSet).mpr (hloc.integrableOn_isCompact hK)
    have hg : Integrable (fun u => M * ‖K.indicator (fun u => u⁻¹) u‖) volume :=
      hIK.norm.const_mul M
    refine hg.mono' (measurable_inv.smul hfdmeas).aestronglyMeasurable ?_
    filter_upwards with u
    by_cases hu : u ∈ K
    · simp only [Set.indicator_of_mem hu]
      calc ‖(u⁻¹ : ℂ) • fderiv ℝ f (z + u)‖ ≤ ‖u⁻¹‖ * ‖fderiv ℝ f (z + u)‖ :=
            norm_smul_le _ _
        _ ≤ ‖u⁻¹‖ * M := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
        _ = M * ‖u⁻¹‖ := by ring
    · rw [Set.indicator_of_notMem hu, norm_zero, mul_zero]
      have hzu : z + u ∉ tsupport f := by
        intro hmem; exact hu ⟨z + u, hmem, by ring⟩
      rw [fderiv_of_notMem_tsupport ℝ hzu, smul_zero, norm_zero]
  have hL := hasFDerivAt_cauchyInt_c1 f hf1 hc z
  set L : ℂ →L[ℝ] ℂ := ∫ u, (u⁻¹ : ℂ) • fderiv ℝ f (z + u) ∂volume with hLdef
  have hfL : fderiv ℝ (cauchyInt f) z = L := by rw [hLdef]; exact hL.fderiv
  have hL1 : L 1 = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) 1) ∂volume := by
    rw [hLdef, ContinuousLinearMap.integral_apply hInt 1]
    apply integral_congr_ae; filter_upwards with u
    simp [smul_eq_mul]
  have hLI : L Complex.I = ∫ u, u⁻¹ * (fderiv ℝ f (z + u) Complex.I) ∂volume := by
    rw [hLdef, ContinuousLinearMap.integral_apply hInt Complex.I]
    apply integral_congr_ae; filter_upwards with u
    simp [smul_eq_mul]
  have hcT : cauchyT f = fun y => c * cauchyInt f y := by
    funext y; rw [hc_def]; exact cauchyT_eq_cauchyInt f y
  have hderiv : fderiv ℝ (cauchyT f) z = c • L := by
    rw [hcT]; exact (hL.const_mul c).fderiv
  have hg1cont : Continuous (fun u => (fderiv ℝ f (z + u)) 1) :=
    ((hf1.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).clm_apply
      continuous_const
  have hg1c : HasCompactSupport (fun u => (fderiv ℝ f (z + u)) 1) :=
    ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft z)).comp_left
      (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
  have hgIcont : Continuous (fun u => (fderiv ℝ f (z + u)) Complex.I) :=
    ((hf1.continuous_fderiv (by simp)).comp (continuous_const.add continuous_id)).clm_apply
      continuous_const
  have hgIc : HasCompactSupport (fun u => (fderiv ℝ f (z + u)) Complex.I) :=
    ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft z)).comp_left
      (g := fun L : ℂ →L[ℝ] ℂ => L Complex.I) (by simp)
  have hg1 : Integrable (fun u => u⁻¹ * (fderiv ℝ f (z + u) 1)) volume :=
    (integrable_mul_inv (fun u => (fderiv ℝ f (z + u)) 1) hg1cont hg1c).congr
      (Filter.Eventually.of_forall (fun u => by ring))
  have hgI : Integrable (fun u => u⁻¹ * (fderiv ℝ f (z + u) Complex.I)) volume :=
    (integrable_mul_inv (fun u => (fderiv ℝ f (z + u)) Complex.I) hgIcont hgIc).congr
      (Filter.Eventually.of_forall (fun u => by ring))
  have hdz : dbarW (cauchyT f) z = c * ∫ u, u⁻¹ * dbarW f (z + u) ∂volume := by
    rw [dbarW, dzbarCoeff, hderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hL1, hLI]
    rw [show (∫ u, u⁻¹ * dbarW f (z + u) ∂volume)
        = (2:ℂ)⁻¹ * ((∫ u, u⁻¹ * (fderiv ℝ f (z + u) 1))
            + Complex.I * (∫ u, u⁻¹ * (fderiv ℝ f (z + u) Complex.I))) by
      rw [show (∫ u, u⁻¹ * dbarW f (z + u) ∂volume)
          = ∫ u, (2:ℂ)⁻¹ * (u⁻¹ * (fderiv ℝ f (z + u) 1)
              + Complex.I * (u⁻¹ * (fderiv ℝ f (z + u) Complex.I))) by
        congr 1 with u; rw [dbarW, dzbarCoeff]; ring]
      rw [integral_const_mul, integral_add hg1 (hgI.const_mul Complex.I), integral_const_mul]]
    ring
  rw [hdz]
  have hcomm : ∫ u, u⁻¹ * dbarW f (z + u) ∂volume = -(Real.pi : ℂ) * f z := by
    rw [← pompeiu f hf1 hc z]
    apply integral_congr_ae; filter_upwards with u; ring
  rw [hcomm, hc_def]
  have hcpi : ((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * (Real.pi : ℂ) = -1 := by
    have h : (-(Real.pi : ℝ)⁻¹) * Real.pi = (-1 : ℝ) := by
      rw [neg_mul, inv_mul_cancel₀ Real.pi_ne_zero]
    rw [← Complex.ofReal_mul, h, Complex.ofReal_neg, Complex.ofReal_one]
  have hstep : ((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * (-(Real.pi : ℂ) * f z)
      = -(((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * (Real.pi : ℂ)) * f z := by ring
  rw [hstep, hcpi]; ring


end Work.Beltrami
