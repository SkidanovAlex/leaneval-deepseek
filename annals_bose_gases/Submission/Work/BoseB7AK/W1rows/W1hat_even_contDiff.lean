import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Submission.Work.BoseB7AK.W1rows.chat_neg
import Submission.Work.BoseB7AK.W1rows.integrable_norm_mul_W1fun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/W1hat_even_contDiff.lean`

**FS `eq:WSestimate`/`lem:DecaychiHat` for the corpus's `Ŵ₁ = chat (W1fun v h ℓ)`:
symmetry and `C¹`-regularity of the one-body Fourier kernel.**

FS §4's one-body kernel `W₁ = g/(χ ⋆ χ(·/ℓ))` is a *real, integrable, compactly
supported* function (`W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g0 v h)`,
supported in `ball 0 R`), and the §10 interface
(`Work.BoseFixR.RView`) pins the mode-indexed kernels to its Fourier transform
`Ŵ₁(k) = chat (W1fun v h ℓ) k`.  Two structural facts about that kernel are used
throughout §10:

* `Ŵ₁` is **even** (`Ŵ₁(−k) = Ŵ₁(k)`), so that the kernels can be evaluated on
  `±k` interchangeably (`Work.BoseB7.Q3Env.W1_even`, the field the §10 estimates
  consume);
* `Ŵ₁` is **`C¹`** (`ContDiff ℝ 1`), so that it is differentiable — the §10
  estimates are phrased against a differentiable kernel.

Both are *free* consequences of "`W₁` is real-valued, `L¹` and has an `L¹` first
moment": the real part of a Fourier integral of a real function is even (taking
the real part of `∫ e^{−i⟪k,y⟫}W₁` kills the odd sine part — no evenness
hypothesis on `W₁` is needed, cf. `Work.BoseB7AK.W1low.chat_eq_integral_cos`),
and `Real.contDiff_fourier` gives `C^N` for a Fourier integral whose moments
`v ↦ ‖v‖^n‖f v‖` are integrable for `n ≤ N`.

## What is proved here

* `contDiff_chat_of_moment` — the general engine: for a real `W` with `W` and
  `v ↦ ‖v‖·‖W v‖` integrable, `chat W` is `C¹`.
* `W1hat_even_contDiff` — the requested row, assembled from

  * `Work.BoseB7AK.W1rows.chat_neg` (evenness, general `W`),
  * `Work.BoseB7AK.W1rows.integrable_norm_mul_W1fun` (the first moment of `W₁`:
    `W₁` is supported in `ball 0 R`, so `‖v‖·‖W₁ v‖ ≤ R·‖W₁ v‖` and
    `Submission.BoseGases.wScaled_g0_integrable` supplies the `L¹` bound).

The analytic content of the second conjunct is *entirely* in
`contDiff_chat_of_moment`; the source-specific work is the moment bound, which is
where the hypotheses `hR`, `hℓ`, `hv_supp`, `h`, `hRℓ` are used (the dilute
regime `R ≤ ℓ·chiR0` is what makes the `(χ⋆χ)`-normalisation bounded below on
`ball 0 R`).
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false

/-- **The `C¹`-engine.**  If a real function `W` and its first moment
`v ↦ ‖v‖·‖W v‖` are integrable, then `Ŵ = chat W` (the real part of the
`p`-convention Fourier transform of `W`) is `C¹`.

`chat W k = Re 𝓕(fun y ↦ (W y : ℂ))((2π)⁻¹ • k)`; `Real.contDiff_fourier`
applied to the complexification of `W` gives `C¹` of the Fourier integral, and
composition with the continuous linear map `k ↦ (2π)⁻¹ • k` and with `Re` (both
`C^∞`) transports it to `chat W`. -/
theorem contDiff_chat_of_moment {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h0 : MeasureTheory.Integrable W)
    (h1 : MeasureTheory.Integrable (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ * ‖W v‖)) :
    ContDiff ℝ 1 (Work.BoseFixR.chat W) := by
  -- the two moment hypotheses, in the shape `Real.contDiff_fourier` consumes
  have hg0 : MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ ^ 0 * ‖(((W v : ℝ) : ℂ))‖) := by
    simpa [Complex.norm_real] using h0.norm
  have hg1 : MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ ^ 1 * ‖(((W v : ℝ) : ℂ))‖) := by
    simpa [Complex.norm_real] using h1
  have hf : ∀ n : ℕ, n ≤ (1 : ℕ∞) → MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ ^ n * ‖(((W v : ℝ) : ℂ))‖) := by
    intro n hn
    have hn' : n ≤ 1 := by simpa using hn
    interval_cases n
    · exact hg0
    · exact hg1
  have hcd : ContDiff ℝ 1 (FourierTransform.fourier
      (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))) :=
    Real.contDiff_fourier hf
  have hlin : ContDiff ℝ 1 ((2 * π)⁻¹ •
      (1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))) :=
    ContinuousLinearMap.contDiff _
  have hcd2 : ContDiff ℝ 1 (fun k : EuclideanSpace ℝ (Fin 3) => FourierTransform.fourier
      (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) ((2 * π)⁻¹ • k)) :=
    hcd.comp hlin
  have hcd3 : ContDiff ℝ 1 (fun k : EuclideanSpace ℝ (Fin 3) => (FourierTransform.fourier
      (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) ((2 * π)⁻¹ • k)).re) :=
    Complex.reCLM.contDiff.comp hcd2
  -- `chat` is this expression (`kinFT` is Mathlib's `𝓕`, rescaled)
  have hfun : Work.BoseFixR.chat W
      = fun k : EuclideanSpace ℝ (Fin 3) => (FourierTransform.fourier
          (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) ((2 * π)⁻¹ • k)).re := by
    funext k
    rw [Work.BoseFixR.chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  rw [hfun]
  exact hcd3

/-- **FS `eq:WSestimate`, Fourier side: the one-body kernel `Ŵ₁ = chat (W1fun v h ℓ)`
is even and `C¹`.**

Evenness is `Work.BoseB7AK.W1rows.chat_neg` (true for *every* real-valued `W`:
the real part of `∫e^{−i⟪k,y⟫}W(y)dy` kills the odd sine part, so no radiality of
`W₁` is involved); `C¹` is `contDiff_chat_of_moment`, whose first-moment
hypothesis is `Work.BoseB7AK.W1rows.integrable_norm_mul_W1fun` — `W₁` is
supported in `ball 0 R`, so `‖v‖‖W₁ v‖ ≤ R‖W₁ v‖`, and `W₁` is `L¹` by
`Submission.BoseGases.wScaled_g0_integrable` (the dilute regime `R ≤ ℓ·chiR0`
bounds `(χ⋆χ)(v/ℓ)` below by `1/2` on `ball 0 R`). -/
theorem W1hat_even_contDiff {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∀ k : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (-k)
          = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k)
      ∧ ContDiff ℝ 1 (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) := by
  refine ⟨fun k => chat_neg (Work.BoseFixR.W1fun v h ℓ) k, contDiff_chat_of_moment ?_ ?_⟩
  · -- `W₁` is `L¹`
    exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  · -- the first moment of `W₁`
    exact integrable_norm_mul_W1fun hR hℓ hv_nonneg hvrad hv_supp h hRℓ

end

end Work.BoseB7AK.W1rows
