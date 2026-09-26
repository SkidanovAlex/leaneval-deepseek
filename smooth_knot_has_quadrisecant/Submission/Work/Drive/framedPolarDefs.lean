import Mathlib
import Submission.AnalyticUnknot
import Submission.Work.Drive.isUnknotted_of_starShapedPolarGraph

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# Framed star-shaped polar graphs: the objects

A *framed* star-shaped polar graph is a curve
`t ↦ c + lam t • (cos (psi t) • f1 + sin (psi t) • f2)` where `(f1, f2)` is an
orthonormal pair of vectors of `Space` (not necessarily the coordinate pair
`(e1, e2)`), `lam` is analytic, `period`-periodic and positive, and `psi` is
analytic with `psi (t + period) = psi t + period` and `deriv psi > 0`.

The unknotting family used for the target statement
`Work.Drive.framedStarShapedPolarGraph` moves the *frame* `(f1, f2)` to the
coordinate frame `(e1, e2)` while at the same time interpolating the polar data
`(lam, psi)` to the round circle: with `g : ℝ → Space × Space` a path of
orthonormal pairs from `(f1, f2)` to `(e1, e2)`,

`framedSlice lam psi c g s t = (1 - s) • c + starRad lam s t • (cos (starAngle psi s t) • (g s).1 + sin (starAngle psi s t) • (g s).2)`

which is the target curve for `s = 0`, the round circle `t ↦ c + cos t • f1 + sin t • f2`
for `s = 1` (when `g 0 = (f1, f2)`), and `standardCircle` for `s = 1` (when `g 1 = (e1, e2)`).

This file contains definitions only; the lemmas about them are proved in
`Submission/Work/Drive/framedStarShapedPolarGraph.lean` and in the companion
files referenced there.
-/

/-- An **orthonormal pair** of vectors of `Space`. -/
def IsOrthoPair (u v : LeanEval.KnotTheory.Quadrisecant.Space) : Prop :=
  ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0

/-- The slice at parameter `s` of the framed star-shaped interpolation, with the
frame taken from a path `g` of orthonormal pairs. -/
noncomputable def framedSlice (lam psi : ℝ → ℝ) (c : LeanEval.KnotTheory.Quadrisecant.Space)
    (g : ℝ → LeanEval.KnotTheory.Quadrisecant.Space × LeanEval.KnotTheory.Quadrisecant.Space)
    (s t : ℝ) : LeanEval.KnotTheory.Quadrisecant.Space :=
  (1 - s) • c +
    starRad lam s t • (Real.cos (starAngle psi s t) • (g s).1 + Real.sin (starAngle psi s t) • (g s).2)

/-- The same slice with the frame `(g s).1, (g s).2` written explicitly. -/
noncomputable def framedCurve (lam psi : ℝ → ℝ) (c u v : LeanEval.KnotTheory.Quadrisecant.Space)
    (s t : ℝ) : LeanEval.KnotTheory.Quadrisecant.Space :=
  (1 - s) • c +
    starRad lam s t • (Real.cos (starAngle psi s t) • u + Real.sin (starAngle psi s t) • v)

lemma framedSlice_eq_framedCurve (lam psi : ℝ → ℝ) (c : LeanEval.KnotTheory.Quadrisecant.Space)
    (g : ℝ → LeanEval.KnotTheory.Quadrisecant.Space × LeanEval.KnotTheory.Quadrisecant.Space)
    (s t : ℝ) :
    framedSlice lam psi c g s t = framedCurve lam psi c (g s).1 (g s).2 s t := rfl

end Work.Drive
