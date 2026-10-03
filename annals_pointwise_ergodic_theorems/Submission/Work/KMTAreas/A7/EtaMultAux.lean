/-
# Auxiliary lemmas for the `η`-cutoff multiplier bound (`Work.KMTAreas.A7.EtaMult`)

The continuous Fourier multiplier `T_φ = 𝓕⁻ ∘ (φ · 𝓕)` of `Work.Analysis.IWMultiplier` is, for a
symbol `φ` which is the Fourier transform of a Schwartz function `K`, the convolution with `K`.
This identification is the only place where Fourier analysis enters the proof that the rescaled
cutoffs `η_{≤k}(θ) = η(θ/2^k)` are uniformly `L^q`-multipliers; the `L^q` bound itself is then
Young's inequality for convolutions.

## Main results

* `Work.KMTAreas.A7.contMulOp_eq_convolution` — `T_φ f = K ⋆ f` when `𝓕 K = φ`.
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le

set_option autoImplicit false
open scoped FourierTransform ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.A7

open Work.Analysis.IWMultiplier (contMulOp)

/-- **The Fourier multiplier `T_φ` is the convolution with the kernel `K` when `𝓕 K = φ`.**  For
`K, f` Schwartz functions and `φ` any function with `𝓕 K = φ` pointwise, the multiplier
`T_φ f = 𝓕⁻ (φ · 𝓕f)` equals the convolution `x ↦ ∫ t, f t * K (x - t) ∂volume`.

The proof identifies `T_φ f` with Mathlib's *Schwartz* convolution `K ⋆ f`, whose defining
property is that its Fourier transform is the pointwise product `𝓕K · 𝓕f`. -/
theorem contMulOp_eq_convolution (K : SchwartzMap ℝ ℂ) (φ : ℝ → ℂ)
    (hφ : ∀ ξ, 𝓕 (K : ℝ → ℂ) ξ = φ ξ) (f : SchwartzMap ℝ ℂ) :
    contMulOp φ (f : ℝ → ℂ)
      = fun x => MeasureTheory.convolution (f : ℝ → ℂ) (K : ℝ → ℂ)
          (ContinuousLinearMap.lsmul ℂ ℂ) volume x := by
  have hfun : ⇑((SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ)) (𝓕 f) (𝓕 K)
        : SchwartzMap ℝ ℂ)
      = fun ξ : ℝ => φ ξ * 𝓕 (f : ℝ → ℂ) ξ := by
    funext ξ
    simp only [SchwartzMap.pairing_apply_apply, SchwartzMap.fourier_coe,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [hφ]; ring
  have key : (fun x => (((SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)) f) K) x)
      = 𝓕⁻ (fun ξ : ℝ => φ ξ * 𝓕 (f : ℝ → ℂ) ξ) := by
    funext ξ
    have hdef : ((SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ)) f) K
        = FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)
            ((SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ)) (𝓕 f) (𝓕 K)) := rfl
    rw [hdef, FourierTransform.fourierInvCLM_apply, SchwartzMap.fourierInv_coe, hfun]
  rw [contMulOp, ← key]
  funext x
  rw [SchwartzMap.convolution_apply]

end Work.KMTAreas.A7
