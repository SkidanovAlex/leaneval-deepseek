import Submission.Work.OddCurve.Free.Step2
import Submission.Work.OddEnvelope.Main

/-!
# The free-tip profile specification

`Work.OddEnvelope.envelopeProfile_spec` records, for an `IsEnvelopeCurve h x y`, everything the
endgame needs to know about the profile `envelopeProfile h x y`: its support, its values at the
ends, positivity and smoothness inside, strict concavity, the two root equations, the sections
being inside, and the non-degeneracy of the sections.  All of it is stated on `[-1, 1]`, because
`IsEnvelopeCurve` normalises the tips to `±1`.

The odd chord curve produced by the paper's construction has its tips at `±ρ(±1)` instead
(`Submission/Work/OddCurve/NOTES_SESSION5.md`), so the free-tip interface needs the same
specification on the *actual* support `[-R₁, R₂]` of the profile.  This file defines that
specification (`ProfileSpecFree`) and proves the easy direction: the tip-normalised spec
(`Work.OddEnvelope.envelopeProfile_spec`) *is* the free spec with `R₁ = R₂ = 1`.  The free spec
for a general `IsEnvelopeCurveFree` is the delegation
`Submission/Work/OddCurve/Free/profileSpecFree`.
-/


/-!
## Caveat: the truncated profile

`Work.OddEnvelope.envelopeProfile` is defined to be `0` outside `[-1, 1]`; for a *free-tip* curve
(whose body has tips at `±ρ(±1)`, `ρ(±1) ≠ 1`) the profile of the body is the **untruncated**
profile `Work.OddVolterra.Free.envProfileFree` (`Submission/Work/OddVolterra/Free/Defs.lean`) —
the two agree on `|t| < 1` (`envProfileFree_eq_envelopeProfile`).  Statements in this file that
mention `envelopeProfile` are therefore the *tip-normalised* ones (correct only when the tips are
`±1`, i.e. `R₁ = R₂ = 1`); the free-tip statements in terms of `envProfileFree` are the sibling's
(`Submission/Work/OddCurveB/FreeTip.lean`, `Submission/Work/OddVolterra/Free/Defs.lean`, which
records `LowSlopeThreeFree`).  The general-interval endgame of this chapter
(`Submission/Work/OddCurve/Free/Endgame.lean`) takes the profile as an explicit hypothesis, so it
is agnostic to this distinction.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- **The profile specification of a free-tip envelope curve.**  `R₁`, `R₂ > 0` are the two tips
of the body (the limits `x s → R₁`, `y s → R₂` as `s → 0⁺`); `f = envelopeProfile h x y` is its
profile.  This is `Work.OddEnvelope.envelopeProfile_spec` without the normalisation `R₁ = R₂ = 1`
(and without the two evenness characterisations, which no consumer uses). -/
def ProfileSpecFree (R₁ R₂ : ℝ) (h x y : ℝ → ℝ) : Prop :=
  Function.support (Work.OddEnvelope.envelopeProfile h x y) ⊆ Set.Icc (-R₁) R₂ ∧
  Work.OddEnvelope.envelopeProfile h x y (-R₁) = 0 ∧
  Work.OddEnvelope.envelopeProfile h x y R₂ = 0 ∧
  (∀ t ∈ Set.Ioo (-R₁) R₂, 0 < Work.OddEnvelope.envelopeProfile h x y t) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddEnvelope.envelopeProfile h x y)
    (Set.Ioo (-R₁) R₂) ∧
  StrictConcaveOn ℝ (Set.Icc (-R₁) R₂) (Work.OddEnvelope.envelopeProfile h x y) ∧
  ContinuousOn (Work.OddEnvelope.envelopeProfile h x y) (Set.Icc (-R₁) R₂) ∧
  (∀ s : ℝ, 0 < s → Work.OddEnvelope.envelopeProfile h x y (y s) = s * y s + h s) ∧
  (∀ s : ℝ, 0 < s →
    Work.OddEnvelope.envelopeProfile h x y (-(x s)) = -(s * (-(x s)) + h s)) ∧
  (∀ s : ℝ, 0 < s → -(x s) ∈ Set.Ioo (-R₁) R₂ ∧ y s ∈ Set.Ioo (-R₁) R₂) ∧
  (∀ s : ℝ, 0 < s → ∀ t ∈ Set.Ioo (-(x s)) (y s),
    0 < Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2)

/-- **The tip-normalised spec is the free spec with `R₁ = R₂ = 1`** — so `ProfileSpecFree` is
non-vacuous and every proved `IsEnvelopeCurve`-statement satisfies it. -/
theorem profileSpecFree_one_one {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) : ProfileSpecFree 1 1 h x y := by
  obtain ⟨hsupp, hl, hr, hpos, hsm, hstr, hcont, hrootr, hrootl, hinside, hnondeg, -, -⟩ :=
    Work.OddEnvelope.envelopeProfile_spec (h := h) (x := x) (y := y) H
  refine ⟨hsupp, hl, hr, hpos, hsm, hstr, hcont, hrootr, hrootl, hinside, ?_⟩
  · intro s hs
    simpa using hnondeg s hs

end

end Free
end Work.OddCurve
