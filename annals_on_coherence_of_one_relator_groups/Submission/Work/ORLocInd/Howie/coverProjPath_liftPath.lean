/-
# The projection of a lifted path, and its invariance under endpoint casts

The covering projection `coverProjPath L u : (Path u v) → (Path u.vert v.vert)`
(`Submission.Work.ORLocInd.Howie.CoverPresentation`) sends a path of the cyclic cover to the
corresponding path of the base graph (arrow by arrow).  This file records the two basic facts
about it that are needed when comparing lifted paths:

* `coverProjPath_cast_vert`: casting a path of the cover along an equality of its endpoints does
  not change its projection (up to the induced cast of the projected path);
* `coverProjPath_liftPath`: the projection of the lift of a base path `p` is `p`.

Together with the injectivity of `coverProjPath` on paths with fixed endpoints
(`coverProjPath_injective`, `Submission.Work.ORLocInd.Howie.coverProjPath_injective`) these let one
prove *equalities* of paths of the cover by computing their projections.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.LiftPathComp
import Submission.Work.ORLocInd.Howie.liftPath_isReduced
import Submission.Work.ORLocInd.Howie.coverProjPath_injective

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- Casting a path of the cyclic cover along equalities of its endpoints does not change its
projection, up to the cast of the projected path along the induced equality of the vertices. -/
theorem coverProjPath_cast_vert (L : Labelling V) {u v v' : CoverVertex L} (hv : v = v')
    (P : Quiver.Path u v) :
    coverProjPath L u (P.cast rfl hv)
      = (coverProjPath L u P).cast rfl (congrArg CoverVertex.vert hv) := by
  cases hv
  rw [Quiver.Path.cast_rfl_rfl, Quiver.Path.cast_rfl_rfl]

/-- Casting a path of the cyclic cover along an equality of the *levels* of its endpoint does not
change its projection.  (Here the two endpoints have the same underlying vertex, so the induced
cast of the projection is a cast along a self-equality and is invisible.) -/
theorem coverProjPath_cast_level (L : Labelling V) {u : CoverVertex L} {b : V} {m m' : ℤ}
    (h : m = m') (P : Quiver.Path u (⟨b, m⟩ : CoverVertex L)) :
    coverProjPath L u (P.cast rfl (coverVertex_level_eq L h)) = coverProjPath L u P := by
  rw [coverProjPath_cast_vert L (coverVertex_level_eq L h) P]
  rw [Quiver.Path.cast_proof_irrel _ rfl rfl _ rfl, Quiver.Path.cast_rfl_rfl]

/-- The projection of the lift of a path of the base graph is the path itself. -/
theorem coverProjPath_liftPath (L : Labelling V) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    coverProjPath L (⟨a, n⟩ : CoverVertex L) (liftPath L p n) = p := by
  induction p with
  | nil =>
      rw [liftPath_nil_cast']
      rw [coverProjPath_cast_vert L (coverVertex_nil_eq L a n)]
      rw [coverProjPath_nil]
      rw [Quiver.Path.cast_proof_irrel _ rfl rfl _ rfl, Quiver.Path.cast_rfl_rfl]
  | cons p e ih =>
      rw [liftPath_cons_cast']
      rw [coverProjPath_cast_vert L (coverVertex_cons_eq L p e n)]
      rw [coverProjPath_cons, ih, coverProjArrow_coverLiftArrow]
      rw [Quiver.Path.cast_proof_irrel _ rfl rfl _ rfl, Quiver.Path.cast_rfl_rfl]

end Work.ORLocInd.Howie
