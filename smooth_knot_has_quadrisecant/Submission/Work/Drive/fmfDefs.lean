import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.genericFullDefs

/-!
# The bad columns of the trisecant locus

This module fixes the vocabulary of the "bad columns" of the lifted trisecant locus
`A = liftedTrisecant r`, i.e. of the columns `ξ` over which the vertical trace of `A` may fail to
be finite.

* `Work.Drive.TangentColumns r` — the columns `ξ` for which some chord `{ξ, ξ+y}` (`0 < y <
  period`) is *tangent* to the knot at one of its endpoints.  Such a column is a limit of
  trisecant columns (`Work.Drive.closure_liftedTrisecant_eq_or_tangent`).
* `Work.Drive.HingeDependent r a b m` — the formal degeneracy of the collinearity map at the
  collinear triple `(a,b,m)`: the two hinge partials `∂_b`, `∂_m` are *dependent*.  This does not
  follow from the rank-two general position (the independent pair may be `(∂_a,∂_b)`), and it is
  exactly the case in which `Work.Drive.local_uniqueness_of_partialsBM_independent` does not apply.
* `Work.Drive.CriticalColumns r` — the columns over which some trisecant is hinge-degenerate.

Nothing is proved here beyond the period-invariance of the hinge partials in the middle variable.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The columns over which some chord is tangent at one of its endpoints. -/
def TangentColumns (r : ℝ → Space) : Set ℝ :=
  {ξ : ℝ | ∃ y : ℝ, 0 < y ∧ y < period ∧
    (cross3 (r (ξ + y) - r ξ) (velocity r ξ) = 0 ∨
     cross3 (r (ξ + y) - r ξ) (velocity r (ξ + y)) = 0)}

/-- The formal degeneracy condition: the two hinge partials of the collinearity map are
dependent. -/
def HingeDependent (r : ℝ → Space) (a b m : ℝ) : Prop :=
  ¬ LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]

/-- The columns over which some trisecant is a "hinge-degenerate" (tangential) trisecant. -/
def CriticalColumns (r : ℝ → Space) : Set ℝ :=
  {ξ : ℝ | ∃ b m : ℝ, 0 < b - ξ ∧ b - ξ < period ∧
    collinearityValue r ξ b m = 0 ∧ r m ∈ openSegment ℝ (r ξ) (r b) ∧ HingeDependent r ξ b m}

/-- The hinge partials are invariant under a translation of the middle parameter by a period. -/
lemma collPartialB_period_middle {r : ℝ → Space} (hr : IsSmoothKnot r) (a b m : ℝ) :
    collPartialB r a b (m + period) = collPartialB r a b m := by
  simp only [collPartialB, hr.periodic m]

/-- The hinge partials are invariant under a translation of the middle parameter by a period. -/
lemma collPartialM_period_middle {r : ℝ → Space} (hr : IsSmoothKnot r) (a b m : ℝ) :
    collPartialM r a b (m + period) = collPartialM r a b m := by
  simp only [collPartialM, hr.velocity_periodic m]

/-- `HingeDependent` only depends on the class of the middle parameter. -/
lemma hingeDependent_add_period {r : ℝ → Space} (hr : IsSmoothKnot r) (a b m : ℝ) :
    HingeDependent r a b (m + period) ↔ HingeDependent r a b m := by
  rw [HingeDependent, HingeDependent, collPartialB_period_middle hr a b m,
    collPartialM_period_middle hr a b m]

end

end Work.Drive
