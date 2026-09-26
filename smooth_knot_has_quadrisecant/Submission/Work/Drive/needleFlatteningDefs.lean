import Mathlib
import Submission.Work.Drive.needleStarShapedAux
import Submission.Work.Drive.needleLowEnd

/-!
# The flattening/polar datum of the needle

The low end of the chord sweep (`Work.Drive.lowEnd_of_projection_starShaped`) consumes, for the
needle `N = Work.Drive.needleFam r D lam δ₁ δ₂ ε`, the following geometric datum:

* a unit vector `w` and a point `c` such that the orthogonal projection
  `M = projectAlong w c N` of the needle onto the plane perpendicular to `w` is **injective on one
  period** and **regular** (its velocity never vanishes);
* a centre `c'` and an orthonormal frame `(u, v)` of that plane in which the projected curve avoids
  `c'`, starts at direction `(1,0)`, has an injective *direction map* about `c'` (the projected
  curve is *star-shaped* about `c'`) and has everywhere **positive angular velocity** about `c'`.

The predicate `Work.Drive.NeedleFlatteningData` below is exactly that datum.  The point of isolating
it is that it is *the whole geometric content* of `Work.Drive.needleStarShapedData` beyond the
regularity of the needle: the `C^∞`, periodicity, injectivity and regularity clauses of
`IsCInfKnot (needleFam ...)` all follow from it (see `Submission/Work/Drive/needleStarShapedDataProved.lean`),
so the two halves of the statement have a single geometric input.

The geometric content of the datum is the *thin concave lens* structure of the needle: with
`w` the normal of the plane of the lens and `(u, v)` the chord frame of the lens, the projection is
a simple closed convex plane curve (the image of the retained arc above, of the chord below, the
two chamfer pieces at the ends), whose profile above the chord is concave in the chord coordinate,
so that every ray from an interior point `c'` meets it exactly once and the curve turns
monotonically about `c'` — a positive angular velocity.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The flattening and polar datum of the needle.**
`NeedleFlatteningData r D lam δ₁ δ₂ ε` is the geometric statement that the needle
`needleFam r D lam δ₁ δ₂ ε` can be flattened into a plane in which it is a star-shaped curve with
positive angular velocity about a suitable centre. -/
def NeedleFlatteningData (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) : Prop :=
  ∃ w c c' u v : Space,
    ‖w‖ = 1 ∧
    Set.InjOn (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) (Set.Ico (0 : ℝ) period) ∧
    (∀ t : ℝ, velocity (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) t ≠ 0) ∧
    ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
    (∀ t : ℝ, projectAlong w c (needleFam r D lam δ₁ δ₂ ε) t - c' =
      inner ℝ (projectAlong w c (needleFam r D lam δ₁ δ₂ ε) t - c') u • u +
      inner ℝ (projectAlong w c (needleFam r D lam δ₁ δ₂ ε) t - c') v • v) ∧
    (∀ t : ℝ, projectAlong w c (needleFam r D lam δ₁ δ₂ ε) t ≠ c') ∧
    polarDir (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) c' u v 0 = (1, 0) ∧
    Set.InjOn (polarDir (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) c' u v)
      (Set.Ico (0 : ℝ) period) ∧
    (∀ t : ℝ, 0 < polarCoord (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) c' u t *
        deriv (polarCoord (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) c' v) t -
      polarCoord (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) c' v t *
        deriv (polarCoord (projectAlong w c (needleFam r D lam δ₁ δ₂ ε)) c' u) t)

end Work.Drive
