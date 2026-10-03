/-
# Erasure commutes with the groupoid multiplication of the free groupoid

The erasure `Work.ORLocInd.Howie.erase D u` sends a path of the span of a datum `D` to the
corresponding path of the ambient graph `Γ`.  Regarded as a prefunctor
(`erasePrefunctor D : SpanVertex D ⥤q V`) it is injective on objects and on arrows and preserves
reversal, so by the general theory of
`Submission/Work/ORBassSerre` (`reducesTo_mapPath`, `qpath_mapPath_isReduced`) it commutes with
deletion of backtracks, hence with reduction `red` and with the groupoid multiplication `pmul`:

`erase (pmul p q) = pmul (erase p) (erase q)`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Span
import Submission.Work.ORBassSerre.Path.Map.reducesTo_mapPath
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Quiver

namespace Hom

variable {U : Type*} [Quiver U] [Quiver.HasReverse U]

/-- `Hom.cast` does not depend on the proofs of the endpoint equalities. -/
theorem cast_irrel {u v u' v' : U} (hu hu' : u = u') (hv hv' : v = v') (e : u ⟶ v) :
    e.cast hu hv = e.cast hu' hv' := by
  rw [Subsingleton.elim hu hu', Subsingleton.elim hv hv']

/-- Casting an arrow along vertex equalities commutes with reversal. -/
theorem cast_reverse {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    Quiver.reverse (e.cast hu hv) = (Quiver.reverse e).cast hv hu := by
  cases hu
  cases hv
  rfl

end Hom

end Quiver

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]

section ErasePrefunctor

variable {P : Presentation V} {v : V} {n : ℕ}

/-- The inclusion of the span of a datum in the ambient graph, as a prefunctor. -/
def erasePrefunctor (D : Datum P v n) : SpanVertex D ⥤q V where
  obj := Subtype.val
  map e := Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom

theorem erasePrefunctor_obj (D : Datum P v n) (u : SpanVertex D) :
    (erasePrefunctor D).obj u = u.1 := rfl

theorem erasePrefunctor_map (D : Datum P v n) {u w : SpanVertex D} (e : u ⟶ w) :
    (erasePrefunctor D).map e = Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom := rfl

/-- The erasure of a path of the span is its image under the erasure prefunctor. -/
theorem erasePrefunctor_mapPath (D : Datum P v n) (u : SpanVertex D) :
    ∀ {w : SpanVertex D} (p : Quiver.Path u w), (erasePrefunctor D).mapPath p = erase D u p := by
  intro w p
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, erase_cons, ih]
      rfl

/-- The erasure prefunctor preserves reversal of arrows. -/
instance erasePrefunctor_mapReverse (D : Datum P v n) : (erasePrefunctor D).MapReverse where
  map_reverse' e := by
    show Quiver.Hom.cast (Quiver.reverse e).2.1 (Quiver.reverse e).2.2.1
        (Quiver.reverse e).1.hom =
      Quiver.reverse (Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom)
    rw [Quiver.Hom.cast_reverse]
    exact Quiver.Hom.cast_irrel _ _ _ _ _

/-- The erasure prefunctor is injective on vertices. -/
theorem erasePrefunctor_obj_injective (D : Datum P v n) :
    Function.Injective (erasePrefunctor D).obj := fun _ _ h => Subtype.ext h

/-- The erasure prefunctor is injective on arrows. -/
theorem erasePrefunctor_map_injective (D : Datum P v n) {u w : SpanVertex D} :
    Function.Injective (fun e : u ⟶ w => (erasePrefunctor D).map e) := by
  intro e f h
  have h1 : HEq (Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom) e.1.hom :=
    Quiver.Hom.cast_heq _ _ _
  have h2 : HEq (Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom)
      (Quiver.Hom.cast f.2.1 f.2.2.1 f.1.hom) := heq_of_eq h
  have h3 : HEq (Quiver.Hom.cast f.2.1 f.2.2.1 f.1.hom) f.1.hom :=
    Quiver.Hom.cast_heq _ _ _
  have hheq : HEq e.1.hom f.1.hom := h1.symm.trans (h2.trans h3)
  exact Subtype.ext (Quiver.Total.ext (e.2.1.trans f.2.1.symm)
    (e.2.2.1.trans f.2.2.1.symm) hheq)

end ErasePrefunctor

section EraseComp

variable {P : Presentation V} {v : V} {n : ℕ}

/-- Erasure is compatible with concatenation of paths. -/
theorem erase_path_comp (D : Datum P v n) (u : SpanVertex D) {w x : SpanVertex D}
    (p : Quiver.Path u w) (q : Quiver.Path w x) :
    erase D u (p.comp q) = (erase D u p).comp (erase D w q) := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, erase_nil, Quiver.Path.comp_nil]
  | cons q e ih =>
      rw [Quiver.Path.comp_cons, erase_cons, erase_cons, Quiver.Path.comp_cons, ih]

/-- Erasure is compatible with deletion of backtracks: it commutes with `red`. -/
theorem erase_path_red (D : Datum P v n) (u : SpanVertex D) {w : SpanVertex D}
    (p : Quiver.Path u w) : erase D u (red p) = red (erase D u p) := by
  have h : red ((erasePrefunctor D).mapPath p) = (erasePrefunctor D).mapPath (red p) :=
    red_eq_of_reducesTo_isReduced
      (Work.ORBassSerre.Path.Map.reducesTo_mapPath (erasePrefunctor D) (reducesTo_red p))
      (Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced (erasePrefunctor D)
        (erasePrefunctor_obj_injective D) (fun {a b} => erasePrefunctor_map_injective D)
        (isReduced_red p))
  rw [← erasePrefunctor_mapPath D u p, ← erasePrefunctor_mapPath D u (red p)]
  exact h.symm

end EraseComp

theorem erase_pmul {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n)
    {u w x : Work.ORLocInd.Howie.SpanVertex D} (p : Quiver.Path u w) (q : Quiver.Path w x) :
    Work.ORLocInd.Howie.erase D u (Work.ORLocInd.Howie.pmul p q) =
      Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.erase D u p)
        (Work.ORLocInd.Howie.erase D w q) := by
  show erase D u (red (p.comp q)) = red ((erase D u p).comp (erase D w q))
  rw [erase_path_red D u (p.comp q), erase_path_comp D u p q]

end Work.ORLocInd.Howie
