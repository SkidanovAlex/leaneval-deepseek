import Mathlib.Analysis.Fourier.Convolution

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fourier transform of a pointwise product is a convolution

For Schwartz functions `f g : 𝓢(E, ℂ)` on a finite-dimensional real inner product space `E`,
the Fourier transform of the pointwise product `f * g` (which is Mathlib's
`SchwartzMap.smulLeftCLM ℂ f g`) is the convolution of the Fourier transforms:

`𝓕 (f * g) ζ = ∫ ξ, 𝓕 f ξ * 𝓕 g (ζ - ξ)`.

This is the dual of `SchwartzMap.fourier_convolution` (`𝓕 (f ⋆ g) = 𝓕 f · 𝓕 g`), obtained by
Fourier inversion.  The route is:

* `𝓕 (𝓕 f) = (fun x ↦ f (-x))` (reflection), proved from `fourierInv_fourier_eq` on Schwartz
  maps together with `Real.fourierInv_eq_fourier_neg`;
* apply `𝓕` to `convolution (mul ℂ ℂ) (𝓕 f) (𝓕 g)` and use `SchwartzMap.fourier_convolution`
  to get the pairing of `𝓕 (𝓕 f)` and `𝓕 (𝓕 g)`, i.e. `x ↦ f (-x) * g (-x)`;
* apply `𝓕⁻` (available on Schwartz maps with no side conditions) and use
  `Real.fourierInv_eq_fourier_comp_neg` to undo the reflection;
* evaluate the Schwartz convolution pointwise with `SchwartzMap.convolution_apply`.
-/

namespace Work.EllipticEst.InteriorRegularity

open FourierTransform MeasureTheory
open scoped SchwartzMap Convolution

theorem fourier_smulLeftCLM_eq_convolution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f g : SchwartzMap E ℂ) :
    FourierTransform.fourier (SchwartzMap.smulLeftCLM ℂ (⇑f) g)
      = fun ζ => ∫ ξ, FourierTransform.fourier f ξ * FourierTransform.fourier g (ζ - ξ) := by
  let F : SchwartzMap E ℂ := 𝓕 f
  let G : SchwartzMap E ℂ := 𝓕 g
  have hA : ⇑F = 𝓕 (⇑f) := SchwartzMap.fourier_coe f
  have hB : ⇑G = 𝓕 (⇑g) := SchwartzMap.fourier_coe g
  have hpairF : 𝓕⁻ F = f := by
    rw [show F = 𝓕 f from rfl]
    exact fourierInv_fourier_eq f
  have hpairG : 𝓕⁻ G = g := by
    rw [show G = 𝓕 g from rfl]
    exact fourierInv_fourier_eq g
  -- `𝓕 (𝓕 f) = fun x ↦ f (-x)`
  have hFF : ∀ x : E, 𝓕 (𝓕 (⇑f)) x = ⇑f (-x) := by
    have h1 : 𝓕⁻ (𝓕 (⇑f)) = ⇑f := by
      have h2 : ⇑(𝓕⁻ F : SchwartzMap E ℂ) = 𝓕⁻ ⇑F := SchwartzMap.fourierInv_coe F
      rw [hA] at h2
      rw [hpairF] at h2
      exact h2.symm
    intro x
    have h3 := Real.fourierInv_eq_fourier_neg (𝓕 (⇑f)) (-x)
    rw [h1, neg_neg] at h3
    exact h3.symm
  have hGG : ∀ x : E, 𝓕 (𝓕 (⇑g)) x = ⇑g (-x) := by
    have h1 : 𝓕⁻ (𝓕 (⇑g)) = ⇑g := by
      have h2 : ⇑(𝓕⁻ G : SchwartzMap E ℂ) = 𝓕⁻ ⇑G := SchwartzMap.fourierInv_coe G
      rw [hB] at h2
      rw [hpairG] at h2
      exact h2.symm
    intro x
    have h3 := Real.fourierInv_eq_fourier_neg (𝓕 (⇑g)) (-x)
    rw [h1, neg_neg] at h3
    exact h3.symm
  have hsmul : ⇑(SchwartzMap.smulLeftCLM ℂ (⇑f) g) = fun x : E => f x * g x := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth f)]
    simp
  -- the Schwartz convolution of `𝓕 f` and `𝓕 g` is the Fourier transform of the product
  have hkey : ⇑(SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) F G)
      = 𝓕 (fun x : E => f x * g x) := by
    have hconv : 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) F G)
        = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 F) (𝓕 G) :=
      SchwartzMap.fourier_convolution _ F G
    have hinv : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) F G
        = 𝓕⁻ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 F) (𝓕 G)
            : SchwartzMap E ℂ) := by
      rw [← hconv]
      exact (fourierInv_fourier_eq
        (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) F G)).symm
    rw [hinv, SchwartzMap.fourierInv_coe]
    have hP : ⇑(SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 F) (𝓕 G))
        = fun x : E => f (-x) * g (-x) := by
      funext x
      rw [SchwartzMap.pairing_apply_apply]
      have e1 : ⇑(𝓕 F : SchwartzMap E ℂ) x = 𝓕 (𝓕 (⇑f)) x := by
        rw [SchwartzMap.fourier_coe F, hA]
      have e2 : ⇑(𝓕 G : SchwartzMap E ℂ) x = 𝓕 (𝓕 (⇑g)) x := by
        rw [SchwartzMap.fourier_coe G, hB]
      rw [e1, e2, hFF x, hGG x]
      rfl
    rw [hP]
    rw [Real.fourierInv_eq_fourier_comp_neg (fun x : E => f (-x) * g (-x))]
    congr 1
    funext x
    rw [neg_neg]
  funext ζ
  rw [SchwartzMap.fourier_coe, hsmul, ← congrFun hkey ζ]
  rw [SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) F G ζ]
  rfl

end Work.EllipticEst.InteriorRegularity
