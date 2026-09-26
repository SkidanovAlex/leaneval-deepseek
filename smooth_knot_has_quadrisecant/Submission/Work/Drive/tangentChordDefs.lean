import Mathlib
import Submission.Work.Drive.genericFullDefs

/-!
# Vocabulary for the local finiteness of the tangent chords

`tangentChordLocallyFinite` (`Submission/Work/Drive/tangentChordLocallyFinite.lean`) states that the
set of *tangent chords* of a smooth knot in tangent-chord general position
(`Work.Drive.TangentChordGP`) is locally finite.  A tangent chord is a pair `(a, h)` with
`0 < h < period` such that the chord joining `r a` and `r (a + h)` is tangent to the knot at `a`
(`Work.Drive.tcSetA`) or at `a + h` (`Work.Drive.tcSetB`).

The tangent condition at `a` is the vanishing of `cross3 (r (a+h) - r a) (deriv r a)`, an equation
in the two variables `(a, h)`.  It is *degenerate on the diagonal* `h = 0` (where the chord
vanishes and `cross3` vanishes identically), and for that reason the analysis is carried out on the
three-dimensional parameter space

    `tcParam = (a, μ, h)`,      `tangentLinePsi r (a, μ, h) = r (a + h) - r a - μ • deriv r a`,

whose zero set is exactly the set of `(a, h)` lying on a tangent line *with the tangency parameter
`μ` recorded*.  At a genuine tangent chord `(a₀, h₀)`, `μ₀` is the scalar with
`r (a₀ + h₀) - r a₀ = μ₀ • deriv r a₀`, so that the chord is *not* on the diagonal, and the
derivative `tangentLinePsiD r p₀` of `tangentLinePsi` is then an isomorphism (the hypothesis
`TangentChordGP` is exactly the non-degeneracy of this derivative, see
`Work.Drive.tangentLinePsiD_injective`).  The implicit function theorem therefore isolates the zero
`p₀` — which is the heart of the local finiteness statement.

This module only fixes the vocabulary; nothing is proved here.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The parameter space of the tangent-line analysis: `(a, μ, h)` records the tangency parameter
`a`, the multiplier `μ` of the tangent and the chord parameter `h`. -/
abbrev tcParam := (ℝ × ℝ) × ℝ

/-- The first coordinate of the parameter triple. -/
def tcF1 : tcParam →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

/-- The second coordinate of the parameter triple. -/
def tcF2 : tcParam →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ

/-- The third coordinate of the parameter triple. -/
def tcF3 : tcParam →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

/-- The sum of the first and third coordinates (the chord parameter `a + h`). -/
def tcSum : tcParam →L[ℝ] ℝ := tcF1 + tcF2

/-- **The tangent-line defect.**  `tangentLinePsi r (a, μ, h) = r (a + h) - r a - μ • deriv r a`;
its zero set is the set of pairs `(a, h)` for which the chord from `r a` to `r (a + h)` lies on the
tangent line at `a`, together with the multiplier `μ` of the tangent direction. -/
def tangentLinePsi (r : ℝ → Space) (q : tcParam) : Space :=
  r (tcSum q) - r (tcF1 q) - tcF3 q • deriv r (tcF1 q)

/-- The (Fréchet) derivative of `tangentLinePsi r` at `p`, written explicitly.  Its three columns
are `r'(a+h) - r'(a) - μ r''(a)`, `-r'(a)` and `r'(a+h)`. -/
def tangentLinePsiD (r : ℝ → Space) (p : tcParam) : tcParam →L[ℝ] Space :=
  tcSum.smulRight (deriv r (tcSum p)) - tcF1.smulRight (deriv r (tcF1 p)) -
    (tcF3 p • tcF1.smulRight (deriv (deriv r) (tcF1 p)) + tcF3.smulRight (deriv r (tcF1 p)))

/-- The set of pairs `(a, h)` with `0 < h < period` whose chord is tangent to the knot at the *first*
endpoint `a`. -/
def tcSetA (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < period ∧
    cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) = 0}

/-- The set of pairs `(a, h)` with `0 < h < period` whose chord is tangent to the knot at the *second*
endpoint `a + h`. -/
def tcSetB (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < period ∧
    cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)) = 0}

end Work.Drive
