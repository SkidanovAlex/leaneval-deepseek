import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.StripCrosscut

/-!
# The consolidated genericity package for the generic reduction

This module fixes the *interface* of the genericity statement that carries every branch of the
generic reduction by approximation (`Submission/Work/Drive/NOTES_genericReduction_approx.md`,
`Submission/Work/Drive/NOTES_noInflection_route.md`):

    TorusGeneralPositionTransverse  ∧  no inflection points  ∧  NoFiveCollinear  ∧
    TangentChordGP

all four achieved *simultaneously* by a `C¹`-small trigonometric perturbation of a given smooth
knot.  `NoFiveCollinear` is the hypothesis that makes the consecutive sub-secants of a quadrisecant
interior-free (so that the collapse resistance applies to them and the limiting quadrisecant cannot
collapse, see `Submission/Work/Drive/consecutive_interiorFree_of_noFiveCollinear.lean`), and
`TangentChordGP` is the non-degeneracy of tangent chords used by the closure form of brick (d)
(`Work.Drive.stripCrosscutAvoidingClosure_of_tangentChordGP`, whose `htc` hypothesis is
`TangentChordGP r` verbatim).

`FiniteMeridianFibre` is the second output needed by that brick: the lifted trisecant locus has a
finite vertical trace over some meridian.  It follows from `TorusGeneralPositionTransverse` plus
`TangentChordGP` (one-dimensional Sard), not from a new genericity density.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **Tangent-chord general position.**  For every chord whose parameter difference lies in one
period: if the chord is parallel to the tangent at one of its endpoints, then it is *not* parallel
to the tangent at the other endpoint and the second-order nondegeneracy
`⟪r'(a) × r''(a), r'(b)⟫ ≠ 0` holds there (and symmetrically at `b`).  This is the hypothesis that
makes a tangent chord a *nondegenerate* limit point of the trisecant locus: exactly one branch of
trisecants arrives at it (implicit function theorem, Jacobian `−Lκw₃/2 ≠ 0`). -/
def TangentChordGP (r : ℝ → Space) : Prop :=
  ∀ a b : ℝ, 0 < b - a → b - a < period →
    (cross3 (r b - r a) (velocity r a) = 0 →
      cross3 (r b - r a) (velocity r b) ≠ 0 ∧
      inner ℝ (cross3 (velocity r a) (deriv (deriv r) a)) (velocity r b) ≠ 0) ∧
    (cross3 (r b - r a) (velocity r b) = 0 →
      cross3 (r b - r a) (velocity r a) ≠ 0 ∧
      inner ℝ (cross3 (velocity r b) (deriv (deriv r) b)) (velocity r a) ≠ 0)

/-- **The consolidated genericity density.**  Every smooth knot has arbitrarily `C¹`-close smooth
approximants that are simultaneously in transverse general position, without inflection points,
without five collinear points, and in tangent-chord general position. -/
def GenericFullDense : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ∀ ε : ℝ, 0 < ε → ∃ r' : ℝ → Space,
    IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      NoFiveCollinear r' ∧ TangentChordGP r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε

/-- **A finite meridian trace of the lifted trisecant locus.**  The hypothesis `hfib` of
`Work.Drive.stripCrosscutAvoidingClosure_of_tangentChordGP` and of
`Work.Drive.stripCrosscutAvoidingO_of_isClosed_finite_fibre`. -/
def FiniteMeridianFibre (r : ℝ → Space) : Prop :=
  ∃ ξ : ℝ, (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite

open LeanEval.KnotTheory.Quadrisecant in
/-- **The four partials of the four-point collinearity map.**  Writing
`Φ₄ a z w b = (cross3 (r z - r a) (r w - r a), cross3 (r z - r a) (r b - r a))` (vanishing of
which says that the four points `r a, r z, r w, r b` are collinear), this is the tuple of the four
directional derivatives `∂_a Φ₄, ∂_z Φ₄, ∂_w Φ₄, ∂_b Φ₄`, each an element of `Space × Space`. -/
def quadPartial (r : ℝ → Space) (a z w b : ℝ) : Fin 4 → Space × Space
  | ⟨0, _⟩ => (cross3 (-(velocity r a)) (r w - r a) + cross3 (r z - r a) (-(velocity r a)),
          cross3 (-(velocity r a)) (r b - r a) + cross3 (r z - r a) (-(velocity r a)))
  | ⟨1, _⟩ => (cross3 (velocity r z) (r w - r a), cross3 (velocity r z) (r b - r a))
  | ⟨2, _⟩ => (cross3 (r z - r a) (velocity r w), 0)
  | _ => (0, cross3 (r z - r a) (velocity r b))

open LeanEval.KnotTheory.Quadrisecant in
/-- **Quadrisecant isolation (Kuperberg, Lemma 2.4 V).**  At every collinear quadruple
`r a, r z, r w, r b` of distinct knot points of one period window, with `r z` and `r w` *strictly*
inside the chord from `r a` to `r b`, the four-point collinearity map `Φ₄` has full rank: its four
partials are linearly independent.

This is the "no five-fold coincidence" condition of Kuperberg's general-position theory: it says that
the four-fold coincidence "four points collinear" is non-degenerate, so the quadrisecants of `r` form
a *discrete* (isolated) periodic set, and the two middle-branches of the trisecant locus cross
*transversally* at each of them.  It is not implied by `TorusGeneralPositionTransverse` (a knot on a
doubly ruled quadric is a counterexample), and it is the extra hypothesis that the corrected `O'`
construction (the passable-quadrisecant rerouting) consumes. -/
def QuadrisecantIsolated (r : ℝ → Space) : Prop :=
  ∀ a z w b : ℝ, 0 < z - a → 0 < w - z → 0 < b - w → b - a < period →
    IsMiddleOnChord r (a : AddCircle period) (b : AddCircle period) (z : AddCircle period) →
    IsMiddleOnChord r (a : AddCircle period) (b : AddCircle period) (w : AddCircle period) →
    LinearIndependent ℝ (quadPartial r a z w b)

open LeanEval.KnotTheory.Quadrisecant in
/-- **The extended genericity package.**  `GenericFullDense` together with quadrisecant isolation
(`QuadrisecantIsolated`, Kuperberg's Lemma 2.4 V).  This is the density statement consumed by the
corrected `O'` construction. -/
def GenericFullDenseK : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ∀ ε : ℝ, 0 < ε → ∃ r' : ℝ → Space,
    IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      NoFiveCollinear r' ∧ TangentChordGP r' ∧ QuadrisecantIsolated r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε ∧
        ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε


end Work.Drive
