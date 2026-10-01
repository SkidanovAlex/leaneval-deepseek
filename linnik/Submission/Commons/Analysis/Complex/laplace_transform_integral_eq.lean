import Mathlib
import Submission.Commons.Analysis.Complex.laplace_inversion_piecewise_C2
import Submission.Commons.Analysis.Complex.laplace_transform_bound_complex
import Submission.Commons.Analysis.Complex.laplace_vertical_endpoint_tendsto

namespace Commons.Analysis.Complex

open MeasureTheory Filter
open scoped Topology

/-- If the symmetric interval integrals `∫ x in (-R)..R, g x` of a function `g : ℝ → ℂ`
converge to `0`, then the Bochner integral of `g` over `ℝ` vanishes.

Indeed, either `g` is integrable, in which case the symmetric interval integrals converge
to `∫ x, g x` and uniqueness of limits gives `∫ x, g x = 0`, or `g` is not integrable,
in which case the Bochner integral is `0` by definition. -/
private lemma integral_eq_zero_of_intervalIntegral_tendsto_zero {g : ℝ → ℂ}
    (h : Tendsto (fun R : ℝ => ∫ x in (-R)..R, g x) atTop (𝓝 0)) :
    ∫ x, g x = 0 := by
  by_cases hg : Integrable g
  · have h1 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, g x) atTop (𝓝 (∫ x, g x)) :=
      intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot tendsto_id
    exact tendsto_nhds_unique h1 h
  · exact integral_undef hg

/-- **Vanishing of the total vertical integral of a Laplace transform.**

For a compactly supported `C²` function `f : ℝ → ℂ` (support inside `[0, x₀]`, with
`f x₀ = 0` and `f 0 = 0`) the full integral over the vertical line `Re z = c` of its
Laplace transform `z ↦ ∫ t in 0..x₀, exp (-(z * t)) * f t` vanishes:
`∫ y, ∫ t in 0..x₀, exp (-((c + y*I) * t)) * f t = 0`.

This is the integrated form of the Fourier-inversion identity `f 0 = (1/2π) ∫ …`; the
Dirichlet-type endpoint limit is supplied by `laplace_vertical_endpoint_tendsto`, which
computes the symmetric partial integrals as `π * f 0 = 0`. -/
theorem laplace_transform_integral_eq {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {c : ℝ} (hc : 0 < c) :
    (∫ y : ℝ, (∫ t : ℝ in (0:ℝ)..x₀,
        Complex.exp (-(((c : ℂ) + (y : ℂ) * Complex.I) * (t : ℂ))) * f t)) = 0 := by
  -- the endpoint value is `π * f 0 = 0`
  have hπ : (Real.pi : ℂ) * f 0 = 0 := by rw [hf0, mul_zero]
  -- the symmetric partial integrals tend to `π * f 0 = 0`
  have htend : Tendsto (fun R : ℝ => ∫ γ in (-R)..R,
      ∫ s in (0:ℝ)..x₀,
        Complex.exp (-(((c : ℂ) + (γ : ℂ) * Complex.I) * (s : ℂ))) * f s)
      atTop (𝓝 0) := by
    have h := laplace_vertical_endpoint_tendsto hx₀ hcont hf2 ⟨B, hBnd⟩ hvan hc
    simpa only [hπ] using h
  exact integral_eq_zero_of_intervalIntegral_tendsto_zero htend

end Commons.Analysis.Complex
