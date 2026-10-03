import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

/-!
# The profile of the rescaled KMT cutoff `η_{≤k}` and its derivative

For the KMT cutoff `η = kmtEta` (a smooth bump supported in `[-1,1]`) and its Littlewood–Paley
dilate `η_{≤k} = etaCut kmtEta k = η(·/2^k)`, the coefficient sequence
`j ↦ cw (η_{≤k}) j = ∫ θ, η_{≤k} θ · e(-jθ) dθ` is the *dilate of the fixed profile*
`φ = 𝓕 η`:

  `cw (η_{≤k}) j = 2^k · φ (2^k · j)`,

with `2^k` the (positive) scale factor.  Since `φ` is the Fourier transform of a smooth compactly
supported function it is a Schwartz function, so this identity turns every bound on the
coefficient sequence into a statement about the single fixed function `φ`, uniformly in `k`.

This file only *defines* the objects (`kmtPhi`, `kmtPsi`, `kmtPhi'`); the three facts about them
(the dilation identity, the differentiability of `φ` and the integrability of `φ'`) are proved in
the sibling files.
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped FourierTransform

/-- The profile `φ = 𝓕 η` of the KMT cutoff: the coefficient sequence of the rescaled cutoff
`η_{≤k}` is its dilate `y ↦ 2^k · φ (2^k y)`. -/
noncomputable def kmtPhi : ℝ → ℂ := FourierTransform.fourier Work.KMTContract.kmtEta

/-- The multiplier `v ↦ -2πi v · η(v)`: the derivative of `φ = 𝓕 η` is the Fourier transform of
this function (`Real.hasDerivAt_fourier`). -/
noncomputable def kmtPsi : ℝ → ℂ :=
  fun v : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (v : ℂ)) * Work.KMTContract.kmtEta v

/-- The derivative profile `φ' = 𝓕 (v ↦ -2πi v · η(v))`. -/
noncomputable def kmtPhi' : ℝ → ℂ := FourierTransform.fourier kmtPsi

end Work.KMTAreas.A7
