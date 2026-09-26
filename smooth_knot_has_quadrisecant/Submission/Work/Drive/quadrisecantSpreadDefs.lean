import Mathlib
import Submission.Work.Drive.Prelude
import Submission.SecantDisk

/-!
# Vocabulary for the generic reduction (Kuperberg §3–§5)

The two analytic inputs of the reduction `Work.Drive.quadrisecant_of_genericCase_noInfl`
(the project lead's steps 1 and 2+3), stated in the vocabulary of the
quadrisecant development.

* `GenericNoInflDense` (step 1): the density of the approximants — every smooth
  knot has arbitrarily C¹-close smooth approximants that are in *transverse
  general position* and have *no inflection points*.  This is a codimension
  count (Kuperberg §1–2); the workspace realisation is
  `Work.Drive.torusGeneralPositionTransverse_noInflection_dense`.

* `SpreadQuadrisecantClose` (steps 2 + 3): for a *knotted* smooth knot `r`
  there are `δ > 0` and a C¹-neighbourhood radius `ε > 0` such that every
  smooth knot `r'` that is C¹-`ε`-close to `r`, in transverse general position
  and without inflections has a quadrisecant whose four parameters are pairwise
  `δ`-separated on the parameter circle.  Route (Kuperberg §3 + §5, fig. 4):
  such an `r'` is knotted (`Work.Drive.isUnknotted_of_close`); the `O'`
  argument gives a topologically non-trivial quadrisecant; the normal-fibre
  embedded disc shows that every secant of length `< ε` is trivial, so the
  three consecutive sub-secants of the quadrisecant have length `≥ ε`; and
  points of the knot at Euclidean distance `≥ ε` are `δ`-separated in
  parameter.

`circSep` is the circular separation of two real parameters, i.e. the distance
of their classes in `AddCircle period`.
-/

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- Circular separation of two real parameters: the distance of their images in
`AddCircle period`. -/
def circSep (x y : ℝ) : ℝ := dist (x : AddCircle period) (y : AddCircle period)

/-- The spread package for a quadruple of real parameters: all four lie in
`[0, period)` and their six pairwise circular separations are `≥ δ`. -/
def SpreadQuad (δ x y z w : ℝ) : Prop :=
  x ∈ Set.Ico 0 period ∧ y ∈ Set.Ico 0 period ∧ z ∈ Set.Ico 0 period ∧
    w ∈ Set.Ico 0 period ∧ δ ≤ circSep x y ∧ δ ≤ circSep x z ∧ δ ≤ circSep x w ∧
    δ ≤ circSep y z ∧ δ ≤ circSep y w ∧ δ ≤ circSep z w

/-- **Step 1**: density of generic non-inflected approximants. -/
def GenericNoInflDense : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ∀ ε : ℝ, 0 < ε → ∃ r' : ℝ → Space,
    IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε

/-- **Steps 2 + 3**: spread quadrisecants of the generic close knots of a
knotted curve. -/
def SpreadQuadrisecantClose : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r →
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' → TorusGeneralPositionTransverse r' →
        (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε) →
        ∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)

/-- **No five collinear knot points.**  In the vocabulary of the quadrisecant
development this is the missing piece of Kuperberg's general position: his
codimension count (§2) excludes five collinear points, and it is exactly what
makes the *consecutive* sub-secants of a quadrisecant interior-free — the
hypothesis without which Kuperberg's "short secant is trivial" lemma
(`Work.Drive.CollapseResistance`) cannot be applied (a chord carrying a fifth
knot point is automatically non-trivial, however short). -/
def NoFiveCollinear (r : ℝ → Space) : Prop :=
  ¬ ∃ c : Fin 5 → AddCircle period, Function.Injective c ∧
      ∃ p v : Space, v ≠ 0 ∧ ∀ i : Fin 5, ∃ a : ℝ, knotMap r (c i) = p + a • v

/-- **Step 1'**: density of generic, non-inflected, five-collinear-free
approximants.  The extra clause is again a codimension count (Kuperberg §2). -/
def GenericNoInflNoFiveDense : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ∀ ε : ℝ, 0 < ε → ∃ r' : ℝ → Space,
    IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧ NoFiveCollinear r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε

/-- **Steps 2 + 3'**: spread quadrisecants of the generic close knots of a
knotted curve, *with the five-collinear-free hypothesis* (without which the
bookkeeping cannot feed the consecutive sub-secants to the collapse resistance,
see `NoFiveCollinear`). -/
def SpreadQuadrisecantNoFiveClose : Prop :=
  ∀ r : ℝ → Space, IsSmoothKnot r → ¬ IsUnknotted r →
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' → TorusGeneralPositionTransverse r' →
        (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
        NoFiveCollinear r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε) →
        ∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
          IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)

end

end Work.Drive
