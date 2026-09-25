/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Plancherel for the convolution, `L¹ ∩ L²` case

**STATUS: fully proven, sorry-free** by the agent working on
`Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2` (session 11).

For `g, k ∈ L¹ ∩ L²`,

  `∫⁻ x, ‖(g * k)(x)‖²  =  ∫⁻ ξ, ‖𝓕g ξ‖² ‖𝓕k ξ‖²`

i.e. the `L²` Plancherel identity for the convolution with both factors in the intersection
`L¹ ∩ L²`.  This is the *shared* infrastructure that the two remaining unproved pieces of the
(3.29) chain need (`within_level_variation_l2` and the `SchwartzMap` form of
`dyadic_square_function_l2` in `Submission/Work/Analysis/Fourier/dilation_variation_scalar_l2.lean`);
the general `L² ⋆ L¹` version follows by density (see
`Submission/Work/Analysis/Fourier/lintegral_convolution_sq_eq_DESIGN.md`).

Auxiliary statements proved here (useful in their own right):
* `fourierInv_fourier_ae_eq` : a.e. Fourier inversion for `h ∈ L¹ ∩ L²` with `𝓕h ∈ L¹ ∩ L²`;
* `memLp_fourier_two` : `𝓕` maps `L¹ ∩ L²` into `L²` (a.e.).
-/
import Mathlib
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.memLp_convolution_one_two
open MeasureTheory
open scoped ENNReal BigOperators Topology FourierTransform RealInnerProductSpace Convolution

namespace Commons.Analysis.Fourier

open Commons.Analysis.Fourier



open Commons.Analysis.Fourier

/-- **Inverse Fourier transform of an `L¹ ∩ L²` function, a.e.** -/
private theorem fourierInv_fourier_ae_eq {h : ℝ → ℂ}
    (h1 : MemLp h 1 (volume : Measure ℝ)) (h2 : MemLp h 2 (volume : Measure ℝ))
    (hF1 : MemLp (fun ξ => 𝓕 h ξ) 1 (volume : Measure ℝ))
    (hF2 : MemLp (fun ξ => 𝓕 h ξ) 2 (volume : Measure ℝ)) :
    (fun x => 𝓕⁻ (𝓕 h) x) =ᵐ[volume] h := by
  have hfwd : ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun ξ => 𝓕 h ξ :=
    fourier_toLp_ae_eq_fourier_of_memLp h1 h2
  have hLp : (𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) = hF2.toLp (fun ξ => 𝓕 h ξ) := by
    rw [Lp.ext_iff]
    exact hfwd.trans (MemLp.coeFn_toLp hF2).symm
  have hinv := fourierInv_toLp_ae_eq_fourierInv (h := fun ξ => 𝓕 h ξ) hF1 hF2
  have hchain : ((𝓕⁻ (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun x => 𝓕⁻ (𝓕 h) x) := by
    have hEq : (𝓕⁻ (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ))
        = 𝓕⁻ (hF2.toLp (fun ξ => 𝓕 h ξ)) := by rw [hLp]
    rw [hEq]
    exact hinv
  have hco : ((𝓕⁻ (𝓕 (h2.toLp h)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (h2.toLp h : ℝ → ℂ) := by
    rw [FourierPair.fourierInv_fourier_eq]
  exact hchain.symm.trans (hco.trans (MemLp.coeFn_toLp h2))

/-- `𝓕` of an `L¹ ∩ L²` function is `L²`. -/
private theorem memLp_fourier_two {h : ℝ → ℂ} (h1 : MemLp h 1 (volume : Measure ℝ))
    (h2 : MemLp h 2 (volume : Measure ℝ)) :
    MemLp (fun ξ => 𝓕 h ξ) 2 (volume : Measure ℝ) := by
  have hcoe : ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 h ξ := fourier_toLp_ae_eq_fourier_of_memLp h1 h2
  exact (Lp.memLp (𝓕 (h2.toLp h))).ae_eq hcoe

/-- **Plancherel for the convolution**, `L¹ ∩ L²` case. -/
theorem lintegral_convolution_sq_eq_of_memLp_one (g k : ℝ → ℂ)
    (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hk1 : MemLp k 1 (volume : Measure ℝ)) (hk2 : MemLp k 2 (volume : Measure ℝ)) :
    ∫⁻ x, ENNReal.ofReal ‖∫ y : ℝ, g y * k (x - y)‖ ^ (2:ℝ)
      = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ * ‖𝓕 k ξ‖) ^ (2:ℝ) := by
  set h : ℝ → ℂ := fun x => ∫ y : ℝ, g y * k (x - y) with hh
  have hgI : Integrable g := memLp_one_iff_integrable.mp hg1
  have hkI : Integrable k := memLp_one_iff_integrable.mp hk1
  have hI : Integrable h := by
    have hconv : h = (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) := by
      funext x; rw [hh, MeasureTheory.convolution_mul]
    rw [hconv]
    exact Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgI hkI
  have h1 : MemLp h 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hI
  have h2 : MemLp h 2 (volume : Measure ℝ) := (memLp_convolution_one_two hg1 hk2).1
  have hF : ∀ ξ : ℝ, 𝓕 h ξ = 𝓕 g ξ * 𝓕 k ξ := by
    intro ξ
    have hconv : h = (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] k) := by
      funext x; rw [hh, MeasureTheory.convolution_mul]
    rw [hconv]
    exact Real.fourier_mul_convolution_eq hgI hkI ξ
  have hFg2 : MemLp (fun ξ => 𝓕 g ξ) 2 (volume : Measure ℝ) := memLp_fourier_two hg1 hg2
  have hFk2 : MemLp (fun ξ => 𝓕 k ξ) 2 (volume : Measure ℝ) := memLp_fourier_two hk1 hk2
  have hprod1 : MemLp (fun ξ => 𝓕 g ξ * 𝓕 k ξ) 1 (volume : Measure ℝ) := by
    have := hFg2.mul (r := 1) hFk2
    refine this.ae_eq (Filter.Eventually.of_forall (fun ξ => ?_))
    simp [mul_comm]
  have hF2 : MemLp (fun ξ => 𝓕 h ξ) 2 (volume : Measure ℝ) := memLp_fourier_two h1 h2
  have hF1 : MemLp (fun ξ => 𝓕 h ξ) 1 (volume : Measure ℝ) :=
    hprod1.ae_eq (Filter.Eventually.of_forall (fun ξ => (hF ξ).symm))
  have hinv : h =ᵐ[volume] fun x => 𝓕⁻ (𝓕 h) x :=
    (fourierInv_fourier_ae_eq h1 h2 hF1 hF2).symm
  calc ∫⁻ x, ENNReal.ofReal ‖h x‖ ^ (2:ℝ)
      = ∫⁻ x, ENNReal.ofReal ‖𝓕⁻ (𝓕 h) x‖ ^ (2:ℝ) := by
        apply lintegral_congr_ae
        filter_upwards [hinv] with x hx
        rw [hx]
    _ = ∫⁻ ξ, ENNReal.ofReal ‖𝓕 h ξ‖ ^ (2:ℝ) :=
        Commons.Analysis.Fourier.lintegral_fourierInv_eq hF1 hF2
    _ = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 g ξ‖ * ‖𝓕 k ξ‖) ^ (2:ℝ) := by
        apply lintegral_congr
        intro ξ
        rw [hF ξ, norm_mul]


end Commons.Analysis.Fourier
