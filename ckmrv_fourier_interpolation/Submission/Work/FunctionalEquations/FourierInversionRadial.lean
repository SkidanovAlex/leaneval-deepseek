import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- The inverse Fourier transform of a Schwartz function, evaluated pointwise, is the
Fourier transform evaluated at the negated point: `𝓕⁻ g y = 𝓕 g (-y)`.

On the Schwartz space the inverse Fourier transform is *defined* as
`g ↦ (𝓕 g) ∘ (-·)`, so this is a restatement of the definition in pointwise form. -/
lemma fourierInv_schwartz_apply {n : ℕ} [NeZero n] (g : 𝓢(E n, ℂ)) (y : E n) :
    (𝓕⁻ g : 𝓢(E n, ℂ)) y = (𝓕 g) (-y) := by
  rw [SchwartzMap.fourierInv_apply_eq, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rfl

/-- **Fourier inversion for radial Schwartz functions.**  On `ℝ^n` the Fourier transform
is an involution up to reflection, `𝓕 (𝓕 f) x = f (-x)`; for a radial `f` the reflection
acts trivially, leaving `𝓕 (𝓕 f) = f`.

This is the involution form of the inversion formula used in the CKMRV proof of the
Fourier interpolation theorem (the reflection is why the interpolation basis is built
from radial functions only). -/
theorem FourierInversionRadial {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (hf : Radial (⇑f))
    (x : E n) :
    FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) x = f x := by
  -- `𝓕⁻ (𝓕 f) = f` together with `𝓕⁻ g y = 𝓕 g (-y)` gives `𝓕 (𝓕 f) (-y) = f y`.
  have hneg : ∀ y : E n, (𝓕 (𝓕 f) : 𝓢(E n, ℂ)) (-y) = f y := by
    intro y
    have h1 : (𝓕⁻ (𝓕 f) : 𝓢(E n, ℂ)) y = (𝓕 (𝓕 f)) (-y) :=
      fourierInv_schwartz_apply (𝓕 f) y
    have h2 : (𝓕⁻ (𝓕 f) : 𝓢(E n, ℂ)) y = f y := by simp
    rw [← h1, h2]
  change (𝓕 (𝓕 f)) x = f x
  have hx : (𝓕 (𝓕 f)) x = f (-x) := by
    have := hneg (-x)
    simpa using this
  rw [hx]
  -- `f` is radial and `‖-x‖ = ‖x‖`, so `f (-x) = f x`.
  exact hf (-x) x (by simp)

end Work.FunctionalEquations
