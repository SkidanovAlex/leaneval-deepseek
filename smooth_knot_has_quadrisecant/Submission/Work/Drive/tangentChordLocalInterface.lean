import Mathlib
import Submission.Work.Drive.strip_defs

/-!
# The local-shape interface at a *tangent chord* (brick (d), generic form)

This module only fixes vocabulary, so that the two delegated pieces of the
free-end lemma (`Submission/Work/Drive/tangentChordLocalCurve.lean` and
`Submission/Work/Drive/localArcAtTangentChord.lean`) can be stated against a common,
sorry-free interface.  Nothing is proved here.

## Mathematical background

Let `r` be a smooth knot and let `A = liftedTrisecant r ⊆ ℝ × (0, period)` be the lifted
trisecant locus.  A point `z ∈ closure A \ A` strictly inside the strip is a *tangent chord*
(`Work.Drive.closure_liftedTrisecant_eq_or_tangent`): writing `a = z.1`, `b = a + z.2`, the
chord joining `r a` and `r b` is tangent to the knot at one of its two endpoints.

Near such a point the trisecant locus is a single arc ending at `z`.  Concretely, the triples
`(x, m, σ)` of *real* parameters with `r x`, `r m`, `r σ` collinear, `|x - a|`, `|m - a|`,
`|σ - b|` small, are exactly

* the *diagonal* triples `m = x` (where collinearity is vacuous), and
* the graph of a curve `g : x ↦ (m(x), σ(x))` through `(a, b)` with derivative `(-1, 0)` at
  `x = a`.

The derivative clause encodes the two facts the consumer needs: `m(x) - x ≈ -2 (x - a)` — the
middle parameter approaches `a` from the side *opposite* to the endpoint `x`, twice as fast —
and `σ(x) → b`.

`TangentChordLocalCurve r a b` below is the abstract form of this local shape, and
`LocalArcAt r z` is the conclusion the strip machinery consumes (local path connectedness of the
traces of `A`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The local shape of the collinearity zero set at the tangent chord `{r a, r b}`.**

There are `δ > 0` and a curve `g : ℝ → ℝ × ℝ` with `g a = (a, b)` and `HasDerivAt g (-1, 0) a`
such that

* every graph point is a collinear triple: `cross3 (r (g x).2 - r x) (r (g x).1 - r x) = 0`;
* conversely, every collinear triple `(x, m, σ)` with `|x - a| < δ`, `|m - a| < δ`,
  `|σ - b| < δ` lies on the diagonal (`m = x`) or on the graph (`(m, σ) = g x`). -/
def TangentChordLocalCurve (r : ℝ → Space) (a b : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℝ → ℝ × ℝ,
    g a = (a, b) ∧
    HasDerivAt g (-1, 0) a ∧
    (∀ x : ℝ, |x - a| < δ → cross3 (r (g x).2 - r x) (r (g x).1 - r x) = 0) ∧
    (∀ x m σ : ℝ, |x - a| < δ → |m - a| < δ → |σ - b| < δ →
      cross3 (r σ - r x) (r m - r x) = 0 → m = x ∨ (m, σ) = g x)

/-- **Local path connectedness of the traces of `A = liftedTrisecant r` at `z`**: there is an
open neighbourhood `O` of `z` such that `O ∩ A` is path connected (in particular nonempty). -/
def LocalArcAt (r : ℝ → Space) (z : ℝ × ℝ) : Prop :=
  ∃ O : Set (ℝ × ℝ), IsOpen O ∧ z ∈ O ∧ IsPathConnected (O ∩ liftedTrisecant r)

end Work.Drive
