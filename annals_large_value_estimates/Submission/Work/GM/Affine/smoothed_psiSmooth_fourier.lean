import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.Fhat_smoothed_kernel
import Submission.Work.GM.Affine.norm_Fhat_conv_le

/-!
# The smoothed function `T ψ(T·) ∗ f` for `ψ = psiSmooth`: continuity, compact support, Fourier

GM §9 smooths a test function `f` by convolving it with the rescaled kernel `T ψ(T ·)`, where
`ψ = psiSmooth` is a smooth bump of total mass `1` supported in `[-1,1]`.  Here we verify the
three structural facts about the smoothing `smoothed psiSmooth T f` that the rest of §9 uses:

* it is continuous;
* it is compactly supported;
* its Fourier transform is `Fhat psiSmooth (ξ/T) · Fhat f ξ`, the product of the Fourier transform
  of the rescaled kernel (computed in `Fhat_smoothed_kernel`) and that of `f`.
-/

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem smoothed_psiSmooth_fourier {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Continuous (smoothed psiSmooth T f) ∧ HasCompactSupport (smoothed psiSmooth T f) ∧
    (∀ ξ : ℝ, Fhat (smoothed psiSmooth T f) ξ = Fhat psiSmooth (ξ / T) * Fhat f ξ) := by
  -- the rescaled kernel `φ(x) = T ψ(T x)`
  set φ : ℝ → ℝ := fun x => T * psiSmooth (T * x) with hφdef
  have hψc : Continuous psiSmooth := psiSmooth_contDiff.continuous
  have hφc : Continuous φ := by
    rw [hφdef]
    exact continuous_const.mul (hψc.comp (continuous_const.mul continuous_id))
  -- `φ` is supported in `[-1/T, 1/T]`, hence compactly supported
  have hφsupp : Function.support φ ⊆ Set.Icc (-(1 / T)) (1 / T) := by
    intro x hx
    rw [Function.mem_support] at hx
    have hx' : psiSmooth (T * x) ≠ 0 := by
      intro h
      exact hx (by rw [hφdef]; simp [h])
    have h1 : T * x ∈ Set.Icc (-1 : ℝ) 1 := psiSmooth_support hx'
    rw [Set.mem_Icc] at h1
    rw [Set.mem_Icc]
    constructor
    · have hle : (-1 : ℝ) / T ≤ x := (div_le_iff₀ hT).mpr (by linarith [h1.1, mul_comm x T])
      rwa [neg_div] at hle
    · exact (le_div_iff₀ hT).mpr (by linarith [h1.2, mul_comm x T])
  have hφcs : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1 / T)) (1 / T)) isCompact_Icc
      hφsupp
  -- `smoothed ψ T f` is the convolution `φ ⋆ f`
  have hφeq : ∀ u, smoothed psiSmooth T f u
      = MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u := by
    intro u
    rw [smoothed, MeasureTheory.convolution_lsmul_swap]
    simp only [smul_eq_mul, hφdef]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    ring
  have hfun : MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      = smoothed psiSmooth T f := funext fun u => (hφeq u).symm
  have hfi : MeasureTheory.Integrable f := hf.integrable_of_hasCompactSupport hcs
  have hφhat : ∀ ξ : ℝ, Fhat φ ξ = Fhat psiSmooth (ξ / T) := by
    intro ξ
    rw [hφdef]
    exact Fhat_smoothed_kernel hT
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume) :=
      hcs.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφc.locallyIntegrable hf
    rwa [hfun] at hcont
  · have hcc : HasCompactSupport (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume) :=
      hφcs.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcs
    rwa [hfun] at hcc
  · intro ξ
    rw [← hfun]
    rw [Fhat_convolution_eq (φ := φ) (f := f) hφc hφcs hfi ξ, hφhat ξ]

end

end Work.GM.Affine
