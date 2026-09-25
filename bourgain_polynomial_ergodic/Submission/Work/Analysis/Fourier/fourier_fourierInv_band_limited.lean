/-
# Band-limitedness of `𝓕⁻ (W φ)` for `W` supported in a band (S3 of Bourgain §7.2)

The lattice comparison (Bourgain (7.4)/(7.5)) requires the scale-family of the major-arc model to be
**pointwise band-limited**: `𝓕 (h k) ξ = 0` for `ξ` outside `[-1/2,1/2]`.  For the model family
`h k = 𝓕⁻ (W k · Φ(t k ·))` this is the statement that the Fourier transform of the inverse transform
of a band-supported function is band-supported.

* `fourier_fourierInv_eq_zero_off_support`.

The proof is three lines: the Fourier inversion formula `Integrable.fourier_fourierInv_eq` gives
`𝓕 (𝓕⁻ (W φ)) ξ = W ξ · φ ξ` at continuity points of `W φ`; and at a point `ξ ∉ Icc (-r) r` the
function `W φ` **vanishes in a neighbourhood** (the complement of the closed band is open), so it is
continuous there, and the value is `0`.

Two remarks for the record (both relevant to §7.2's S3):

* the two integrability hypotheses are really needed: Fourier inversion in this form requires
  `Integrable (W φ)` **and** `Integrable (𝓕 (W φ))`.  For a **sharp** cutoff (`W = amplitude · 1_{|β|≤r}`)
  the second hypothesis *fails*, because `𝓕(W φ)` then decays only like `|x|^{-1}`.  With a **smooth**
  cutoff `ψ` (Bourgain's `φ(Dβ)`) the product is smooth and compactly supported, its Fourier transform
  is Schwartz, and both hypotheses hold.  This is the reason Bourgain's §7 truncation is a smooth bump
  and not an indicator: the sharp-cutoff model of §6 is *unusable* for the lattice comparison, and the
  sharp-to-smooth replacement must be paid for by an error term.
* no continuity hypothesis on `W` or `φ` is needed (the older filed version of this statement carried
  `Measurable`/continuity hypotheses that the application cannot supply, and lacked the integrability
  hypothesis that it can).
-/

import Mathlib

open MeasureTheory
open scoped FourierTransform

namespace Commons.Analysis.Fourier

theorem fourier_fourierInv_eq_zero_off_support {r : ℝ} {W φ : ℝ → ℂ}
    (hW : ∀ ξ, ξ ∉ Set.Icc (-r) r → W ξ = 0)
    (hf : MeasureTheory.Integrable (fun ξ => W ξ * φ ξ))
    (hfi : MeasureTheory.Integrable (𝓕 (fun ξ => W ξ * φ ξ))) :
    ∀ ξ : ℝ, ξ ∉ Set.Icc (-r) r → 𝓕 (𝓕⁻ (fun ξ => W ξ * φ ξ)) ξ = 0 := by
  intro ξ hξ
  have hcont : ContinuousAt (fun ξ => W ξ * φ ξ) ξ := by
    have hopen : IsOpen (Set.Icc (-r) r)ᶜ := isClosed_Icc.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hξ)
    refine ContinuousAt.congr (f := fun _ : ℝ => (0:ℂ)) continuousAt_const ?_
    filter_upwards [Metric.ball_mem_nhds ξ hε] with y hy
    rw [hW y (hball hy)]
    simp
  rw [MeasureTheory.Integrable.fourier_fourierInv_eq hf hfi hcont]
  exact mul_eq_zero_of_left (hW ξ hξ) _

end Commons.Analysis.Fourier
