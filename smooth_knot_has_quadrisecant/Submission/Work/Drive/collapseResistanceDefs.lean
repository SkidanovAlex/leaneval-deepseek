import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.secantDiskAPI

/-!
# Collapse resistance for quadrisecants of approximants (Kuperberg §6, fig. 4)

This module fixes the *vocabulary* of the missing geometric input of the generic reduction by
approximation (`Work.Drive.quadrisecant_of_genericCase_approx`): Kuperberg's collapse-resistance
statement that a *short* and *narrow* secant of a knot close to `r` is topologically trivial.

## The mathematics

Let `r` be a smooth knot.  In a tubular neighbourhood of `r` (radius `ρ`) every point `s` has
normal coordinates: `s = r x + a • n x + b • m x` for a unique base parameter `x` and normal
components `(a,b)`, `|a|, |b| < ρ`, where `(n x, m x)` is a unit normal frame of `r`.

Let `r'` be a knot `C¹`-close to `r`, and let `σ = (A,B)` be a secant of `r'` whose chord is
*short* (spatial length `< δ`) and whose two parameters are *close on the parameter circle*
(`dist A B < δ`, so that the arc of `r'` between them stays in the same small ball), and assume the
chord has no knot point strictly inside it (`ChordInteriorFree`).  Then `σ` is **trivial**.

Proof (Kuperberg §6, fig. 4): the chord and the corresponding short arc of `r'` lie in a small
ball inside the tubular neighbourhood, and the knot meets each *fibre* of the tube (the flat normal
disk `{r x + a n x + b m x}`) at most once — `r'` is a *section* of the tube, because a fibre meets
`r'` only at parameters near its base (a fibre is transverse to `r` and `r'` is `C¹`-close to `r`).
For every point `α u` of the knot arc between the two endpoints, let `c u` be the point where the
chord meets the fibre through `α u`.  The ruled surface `D (u,v) = (1−v) • α u + v • c u` is a
continuous disk whose boundary is the arc (at `v = 0`) and the chord (at `v = 1`), and whose
interior consists of points strictly inside fibres; since the only point of `r'` in the fibre
through `α u` is `α u` itself, the interior misses the knot.  Hence the arc together with the chord
bounds a disk with interior off the knot: `TrivialSecant r' A B`.

## Formalisation status

The statement below is stated in the vocabulary that already exists in this worktree
(`IsSmoothKnot`, `knotMap`, `velocity`, `TrivialSecant`, `ChordInteriorFree`, `dist`), so it can be
proved without naming the tubular neighbourhood: the tube and the section property are *derived* in
the proof.  The two ingredients isolated by the argument above are

* `Work.Drive.normalTube_of_smoothKnot`: the existence of the normal-coordinate system (flat fibres,
  injective on the tube, covering a neighbourhood of the knot) — a classical tubular-neighbourhood
  theorem for a compact embedded curve, not in Mathlib;
* `Work.Drive.normalTube_section_of_close`: a `C¹`-close knot is a section of that tube.

The consumer of this statement is
`Work.Drive.spreadQuadrisecantClose_of_nontrivial_and_collapse`
(`Submission/Work/Drive/quadrisecant_of_genericCase_approx.lean`), which uses it in the form

    non-trivial secant  +  interior-free  +  narrow  ⟹  the chord is long,

to bound the four points of a quadrisecant of an approximant away from collapse.  That is exactly
the use Kuperberg makes of it in §6 ("We must show that the endpoints and middle points of the
quadrisecants do not converge together").
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **Collapse resistance (Kuperberg §6, fig. 4).**  For every smooth knot `r` there are `ε > 0`
and `δ > 0` with the following property: if `r'` is a smooth knot within the `C¹`-`ε`-ball of `r`,
and the secant `(A,B)` of `r'` is *narrow* (`dist A B < δ`), *short*
(`‖knotMap r' A - knotMap r' B‖ < δ`) and *interior-free* (no knot point strictly inside the chord),
then `(A,B)` is a topologically trivial secant of `r'`.

This is the statement that keeps the four points of a quadrisecant of an approximant away from
collapse: its contrapositive says that a *non-trivial* interior-free secant of a `C¹`-close knot is
either long or wide, and in the limiting argument (`Work.Drive.quadrisecantChord_of_tendsto_quadrisecants`)
only the parameters matter, so a uniform bound is obtained. -/
def CollapseResistance : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r →
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε) →
        ∀ A B : AddCircle period,
          dist A B < δ → ‖knotMap r' A - knotMap r' B‖ < δ →
            ChordInteriorFree r' A B → TrivialSecant r' A B

end Work.Drive
