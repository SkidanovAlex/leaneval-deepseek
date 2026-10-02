import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Beltrami.cauchyTransform_contDiff
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.Cauchy.isDbarDeriv_cauchy_of_integrable
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_unique
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_of_contDiff_of_ne_zero_hasCompactSupport
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal Convolution

/-- If `B` is continuous with compact support then, for every `z`, the function
`t ↦ t⁻¹ * B (z - t)` is integrable: it is the product of the locally integrable kernel
`t ↦ t⁻¹` with the continuous compactly supported function `t ↦ B (z - t)`. -/
private lemma integrable_inv_mul_comp_hasCompactSupport (B : ℂ → ℂ) (hBc : Continuous B)
    (hBs : HasCompactSupport B) (z : ℂ) : Integrable (fun t : ℂ => t⁻¹ * B (z - t)) := by
  have hcs : HasCompactSupport (fun t : ℂ => B (z - t)) :=
    hBs.comp_isClosedEmbedding (Homeomorph.subLeft z).isClosedEmbedding
  have hcont : Continuous (fun t : ℂ => B (z - t)) := hBc.comp (continuous_const.sub continuous_id)
  have h := Work.MRMT.Beltrami.locallyIntegrable_inv_complex.integrable_smul_left_of_hasCompactSupport
    hcont hcs
  refine h.congr ?_
  filter_upwards with t
  rw [smul_eq_mul, mul_comm]

/-- **The pointwise `∂`-identity `∂(C h) = C(∂h)`.**

For `h` of class `C¹` with compact support and every `z : ℂ`,
`Work.MRMT.dz (cauchyTransform h) z = cauchyTransform (fun w => dz h w) z`.

The Cauchy transform is a convolution with the locally integrable kernel `t ↦ t⁻¹`
(`cauchyTransform_eq_neg_const_mul_convolution`), so its Fréchet derivative is given by
Mathlib's `HasCompactSupport.hasFDerivAt_convolution_right`: the derivative at `z` is
`(t ↦ t⁻¹) ⋆[precompR] (fderiv ℝ h)` evaluated at `z`, i.e. the linear map
`v ↦ ∫ t, t⁻¹ * (fderiv ℝ h (z - t)) v`.  Extracting `∂` (evaluating at `1` and `I`)
turns each summand into `∫ t, t⁻¹ * (fderiv ℝ h (z - t)) 1` etc., and the pointwise identity
`fderiv ℝ h w 1 - I * fderiv ℝ h w I = 2 * dz h w` identifies the sum with
`∫ t, t⁻¹ * dz h (z - t)`, which is the Cauchy transform of `∂h` by the same convolution
identity. -/
private lemma cauchyTransform_dz_eq {h : ℂ → ℂ} (hc : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    ∀ z : ℂ, dz (cauchyTransform h) z = cauchyTransform (fun w => dz h w) z := by
  intro z
  have hfd : Continuous (fderiv ℝ h) := hc.continuous_fderiv (by norm_num)
  have hcont_dz : Continuous (dz h) := by
    unfold dz
    exact ((hfd.clm_apply continuous_const).sub
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  have hcs_dz : HasCompactSupport (dz h) := by
    have h1 : HasCompactSupport (fun w : ℂ => fderiv ℝ h w (1 : ℂ)) := hs.fderiv_apply ℝ 1
    have hI : HasCompactSupport (fun w : ℂ => fderiv ℝ h w Complex.I) := hs.fderiv_apply ℝ Complex.I
    have h2 : HasCompactSupport (fun w : ℂ => Complex.I * fderiv ℝ h w Complex.I) :=
      hI.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
    have h3 : HasCompactSupport
        (fun w : ℂ => fderiv ℝ h w (1 : ℂ) - Complex.I * fderiv ℝ h w Complex.I) := h1.sub h2
    have h4 := h3.comp_left (g := fun w : ℂ => w / 2) (by simp)
    show HasCompactSupport
      (fun x : ℂ => ((fderiv ℝ h x) 1 - Complex.I * (fderiv ℝ h x) Complex.I) / 2)
    exact h4
  have hintD1 : Integrable (fun t : ℂ => t⁻¹ * (fderiv ℝ h (z - t) 1)) :=
    integrable_inv_mul_comp_hasCompactSupport (fun w => fderiv ℝ h w 1)
      (hfd.clm_apply continuous_const) (hs.fderiv_apply ℝ 1) z
  have hintDI : Integrable (fun t : ℂ => t⁻¹ * (fderiv ℝ h (z - t) Complex.I)) :=
    integrable_inv_mul_comp_hasCompactSupport (fun w => fderiv ℝ h w Complex.I)
      (hfd.clm_apply continuous_const) (hs.fderiv_apply ℝ Complex.I) z
  -- the Fréchet derivative of `C h` at `z`, as given by the convolution theorem
  let A : ℂ →L[ℝ] ℂ :=
    ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.mul ℝ ℂ),
      volume] fderiv ℝ h) z
  have hD0 : HasFDerivAt ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] h) A z :=
    hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      Work.MRMT.Beltrami.locallyIntegrable_inv_complex hc z
  have hD : HasFDerivAt (cauchyTransform h)
      ((ContinuousLinearMap.mul ℝ ℂ (-cauchyConst)).comp A) z := by
    refine ((ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.mul ℝ ℂ (-cauchyConst))).comp z hD0).congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Work.MRMT.Beltrami.cauchyTransform_eq_neg_const_mul_convolution h]
    rfl
  have hA1 : A 1 = ∫ t, t⁻¹ * (fderiv ℝ h (z - t) 1) := by
    rw [show A = ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.precompR ℂ
        (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ h) z from rfl]
    rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
        Work.MRMT.Beltrami.locallyIntegrable_inv_complex (hs.fderiv ℝ)
        (hc.continuous_fderiv (by norm_num)) z 1]
    rw [MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with t
    simp
  have hAI : A Complex.I = ∫ t, t⁻¹ * (fderiv ℝ h (z - t) Complex.I) := by
    rw [show A = ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.precompR ℂ
        (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ h) z from rfl]
    rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
        Work.MRMT.Beltrami.locallyIntegrable_inv_complex (hs.fderiv ℝ)
        (hc.continuous_fderiv (by norm_num)) z Complex.I]
    rw [MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with t
    simp
  have hkey : A 1 - Complex.I * (A Complex.I) = 2 * ∫ t, t⁻¹ * (dz h (z - t)) := by
    rw [hA1, hAI, ← integral_const_mul]
    rw [← integral_sub hintD1 (hintDI.const_mul Complex.I)]
    rw [show (fun t : ℂ => t⁻¹ * (fderiv ℝ h (z - t)) 1
          - Complex.I * (t⁻¹ * (fderiv ℝ h (z - t)) Complex.I))
        = fun t => t⁻¹ * (2 * dz h (z - t)) from by
      funext t; simp only [dz]; ring]
    rw [show (fun t : ℂ => t⁻¹ * (2 * dz h (z - t))) = fun t => 2 * (t⁻¹ * dz h (z - t)) from by
      funext t; ring]
    rw [integral_const_mul]
  have hstep : (((ContinuousLinearMap.mul ℝ ℂ (-cauchyConst)).comp A) 1
        - Complex.I * (((ContinuousLinearMap.mul ℝ ℂ (-cauchyConst)).comp A) Complex.I)) / 2
      = (-cauchyConst) * ∫ t, t⁻¹ * dz h (z - t) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [show (ContinuousLinearMap.mul ℝ ℂ (-cauchyConst)) (A 1) - Complex.I *
          ((ContinuousLinearMap.mul ℝ ℂ (-cauchyConst)) (A Complex.I))
        = (-cauchyConst) * (A 1 - Complex.I * (A Complex.I)) by
      simp only [ContinuousLinearMap.mul_apply']; ring]
    rw [hkey]; ring
  rw [show dz (cauchyTransform h) z
      = (fderiv ℝ (cauchyTransform h) z 1
          - Complex.I * fderiv ℝ (cauchyTransform h) z Complex.I) / 2 from rfl,
    hD.fderiv, hstep]
  rw [Work.MRMT.Beltrami.cauchyTransform_eq_neg_const_mul_convolution (fun w => dz h w)]
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']

theorem cauchyTransform_contDiff_one {h : ℂ → ℂ} (hc : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    ContDiff ℝ 1 (cauchyTransform h) ∧
      (∀ z : ℂ, dzbar (cauchyTransform h) z = h z) ∧
      (∀ z : ℂ, dz (cauchyTransform h) z = cauchyTransform (fun w => dz h w) z) := by
  have hcd1 : ContDiff ℝ 1 (cauchyTransform h) := by
    have hconv := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      Work.MRMT.Beltrami.locallyIntegrable_inv_complex hc
    rw [Work.MRMT.Beltrami.cauchyTransform_eq_neg_const_mul_convolution h]
    exact hconv.const_smul (- Work.MRMT.cauchyConst)
  refine ⟨hcd1, ?_, cauchyTransform_dz_eq hc hs⟩
  intro z
  have hint : Integrable h volume := hc.continuous.integrable_of_hasCompactSupport hs
  have hweak1 : IsDbarDeriv (cauchyTransform h) h :=
    Work.MRMT.Cauchy.isDbarDeriv_cauchy_of_integrable h hint
  have hweak2 : IsDbarDeriv (cauchyTransform h) (dzbar (cauchyTransform h)) :=
    Work.MRMT.Weyl.isDbarDeriv_dzbar hcd1 (by norm_num)
  have hae : dzbar (cauchyTransform h) =ᵐ[volume] h :=
    Work.MRMT.Sobolev.is_dbar_deriv_unique hweak2 hweak1
  have hcontD : Continuous (dzbar (cauchyTransform h)) :=
    Work.MRMT.Sobolev.continuous_dzbar_of_contDiff (cauchyTransform h) (by norm_num) hcd1
  have heq : dzbar (cauchyTransform h) = h :=
    MeasureTheory.Measure.eq_of_ae_eq hae hcontD hc.continuous
  exact congrFun heq z

end Work.MRMT.Found
