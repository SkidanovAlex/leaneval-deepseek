/-
# Erasure preserves and reflects reducedness of paths

The erasure `erase D u : Quiver.Path u w → Quiver.Path u.1 w.1` of a path of the span of a datum
`D` into the ambient graph `Γ` is the action on paths of the *inclusion prefunctor*
`erasePrefunctor D : SpanVertex D ⥤q V` (`Submission.Work.ORLocInd.Howie.erase_pmul`).  Since that
prefunctor

* preserves reversal (`erasePrefunctor_mapReverse`) and
* is injective on vertices (`erasePrefunctor_obj_injective`) and on arrows
  (`erasePrefunctor_map_injective`),

the general theory of `Submission.Work.ORBassSerre` gives both directions of

`(erase D u p).IsReduced ↔ p.IsReduced`:

* a backtrack of `p` is mapped to a backtrack of `erase D u p`
  (`Work.ORBassSerre.Path.Map.deleteBacktrack_mapPath`), so a non-reduced `p` has a non-reduced
  erasure;
* a backtrack of `erase D u p` would come from a backtrack of `p`
  (`Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced`, the injectivity argument), so a reduced `p`
  has a reduced erasure.

This file records the resulting equivalence, which is what the Howie development needs.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Span
import Submission.Work.ORLocInd.Howie.erase_pmul

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]

section EraseIsReduced

variable {P : Presentation V} {v : V} {n : ℕ}

/-- Erasure of a path of the span is the action on paths of the inclusion prefunctor. -/
theorem erase_eq_mapPath (D : Datum P v n) {u w : SpanVertex D} (p : Quiver.Path u w) :
    erase D u p = (erasePrefunctor D).mapPath p :=
  (erasePrefunctor_mapPath D u p).symm

/-- A non-reduced path of the span has a non-reduced erasure: the erasure prefunctor preserves
reversal, hence sends a deletable backtrack to a deletable backtrack. -/
theorem not_isReduced_erase (D : Datum P v n) {u w : SpanVertex D} (p : Quiver.Path u w)
    (hp : ¬ p.IsReduced) : ¬ (erase D u p).IsReduced := by
  intro hred
  apply hp
  intro q hq
  have h := Work.ORBassSerre.Path.Map.deleteBacktrack_mapPath (erasePrefunctor D) hq
  rw [← erase_eq_mapPath D p, ← erase_eq_mapPath D q] at h
  exact hred (erase D u q) h

/-- A reduced path of the span has a reduced erasure: the erasure prefunctor is injective on
vertices and on arrows and preserves reversal, so a backtrack in the erasure would come from a
backtrack in the path itself. -/
theorem isReduced_erase (D : Datum P v n) {u w : SpanVertex D} (p : Quiver.Path u w)
    (hp : p.IsReduced) : (erase D u p).IsReduced := by
  rw [erase_eq_mapPath D p]
  exact Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced (erasePrefunctor D)
    (erasePrefunctor_obj_injective D) (fun {a b} => erasePrefunctor_map_injective D) hp

/-- A path of the span with reduced erasure is reduced. -/
theorem isReduced_of_isReduced_erase (D : Datum P v n) {u w : SpanVertex D}
    (p : Quiver.Path u w) (hp : (erase D u p).IsReduced) : p.IsReduced := by
  by_contra h
  exact not_isReduced_erase D p h hp

end EraseIsReduced

theorem erase_isReduced {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) {u w : Work.ORLocInd.Howie.SpanVertex D}
    (p : Quiver.Path u w) :
    (Work.ORLocInd.Howie.erase D u p).IsReduced ↔ p.IsReduced :=
  ⟨fun h => isReduced_of_isReduced_erase D p h, fun h => isReduced_erase D p h⟩

end Work.ORLocInd.Howie
