import Mathlib
import Submission.Commons.Analysis.Fourier.convolution_kernel_fubini
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform

/-- **Pointwise multiplier form of the iterated-integral band operator.**
For a bounded measurable frequency set `C` and `f ∈ L¹ ∩ L²`,
`∫ y, f y · ∫_θ 1_C(θ) e^{-i(x-y)θ} dθ = 2π · (𝓕⁻ (1_{C̃} · 𝓕 f)) x`
where `C̃ = {ξ : ℝ | -2π ξ ∈ C}` and `bandOp C̃ f = 𝓕⁻ (1_{C̃} · 𝓕 f)` is the commons band-pass
operator.  This is `convolution_kernel_fubini` with the multiplier `M = 1_C`. -/
theorem iterated_integral_eq_bandOp (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (f : ℝ → ℂ)
    (hf1 : MeasureTheory.MemLp f 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hf2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    (∫ y : ℝ, f y * (∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = 2 * Real.pi * bandOp {ξ : ℝ | -(2 * Real.pi) * ξ ∈ C} f x := by
  -- The frequency set produced by `iterated_eq_fourierInv` uses `-2π·ξ`; the target set uses
  -- `-(2π)·ξ`.  They are the same set, and hence the same indicator multiplier.
  have hset : {ξ : ℝ | -2 * Real.pi * ξ ∈ C} = {ξ : ℝ | -(2 * Real.pi) * ξ ∈ C} := by
    ext ξ
    simp only [Set.mem_setOf_eq]
    rw [show -2 * Real.pi * ξ = -(2 * Real.pi) * ξ by ring]
  have hfun : (fun ξ : ℝ => Set.indicator {ξ : ℝ | -2 * Real.pi * ξ ∈ C}
        (fun ξ => (𝓕 f) ξ) ξ)
      = Set.indicator {ξ : ℝ | -(2 * Real.pi) * ξ ∈ C} (𝓕 f) := by
    rw [hset]
  rw [iterated_eq_fourierInv f (memLp_one_iff_integrable.mp hf1) C hC hbd.measure_lt_top x, hfun]
  rfl

end Commons.Analysis.Fourier
