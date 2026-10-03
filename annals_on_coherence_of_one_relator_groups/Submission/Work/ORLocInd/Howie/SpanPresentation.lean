/-
# The sub-presentation spanned by a datum (Howie 2000, step 1)

This file assembles the *presentation* structure of the sub-quiver spanned by a datum
(`Submission.Work.ORLocInd.Howie.Span`):

* the relators are the relators of `P` that occur in the datum (`UsedRelator`);
* the base vertex of such a relator is the corresponding vertex of the span, and its closed path is
  the corresponding path of the span (`spanBase`, `spanPath`);
* the code of an unoriented edge of the span is inherited from `P` (`spanEdgeOf`).

The resulting `spanPresentation D : Presentation (SpanVertex D)` is a presentation of the groupoid
`⟨Γ₀ | R₀⟩` of Howie's step 1: `Γ₀` is the subgraph of `Γ` spanned by the datum and `R₀` the set of
relators occurring in it.  On top of this file one transports the datum to the span and proves the
transfer of the vanishing statement.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Span
import Submission.Work.ORLocInd.Howie.erase_pathToSpan
import Submission.Work.ORLocInd.Howie.erase_pmul
import Submission.Work.ORLocInd.Howie.erase_isReduced
import Submission.Work.ORLocInd.Howie.erase_comp
import Submission.Work.ORLocInd.Howie.erase_compPower
import Submission.Work.ORLocInd.Howie.pathToSpan_arrowList
import Submission.Work.ORLocInd.Howie.span_noSelfLoop
import Submission.Work.ORLocInd.Howie.isReduced_compPower_of_comp_self

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
variable {P : Presentation V} {v : V} {n : ℕ}

/-- The relators of `P` occurring in the datum `D`. -/
def UsedRelator (D : Datum P v n) (i : P.ι) : Prop :=
  ∃ (j : Fin n) (t : RelatorTerm P v), t ∈ D.terms j ∧ t.i = i

theorem usedRelator_of_mem_terms {D : Datum P v n} {j : Fin n} {t : RelatorTerm P v}
    (ht : t ∈ D.terms j) : UsedRelator D t.i := ⟨j, t, ht, rfl⟩

theorem mem_visitedList_base_of_usedRelator {D : Datum P v n} {i : P.ι}
    (hi : UsedRelator D i) : P.base i ∈ D.visitedList := by
  obtain ⟨j, t, ht, rfl⟩ := hi
  exact D.mem_visitedList_of_mem_term_relator ht (Quiver.Path.mem_vertices_head (P.path t.i))

theorem inSpan_relator {D : Datum P v n} {i : P.ι} (hi : UsedRelator D i) :
    InSpan D (P.path i) := by
  obtain ⟨j, t, ht, rfl⟩ := hi
  exact ⟨fun x hx => D.mem_visitedList_of_mem_term_relator ht hx,
    fun e he => D.mem_usedArrowsList_of_mem_term ht (Or.inr he)⟩

theorem inSpan_gamma (D : Datum P v n) (j : Fin n) : InSpan D (D.γ j).1 :=
  ⟨fun x hx => D.mem_visitedList_of_mem_gamma j hx,
    fun e he => D.mem_usedArrowsList_of_mem_gamma j he⟩

theorem inSpan_delta (D : Datum P v n) {j : Fin n} {t : RelatorTerm P v} (ht : t ∈ D.terms j) :
    InSpan D t.δ :=
  ⟨fun x hx => D.mem_visitedList_of_mem_term_delta ht hx,
    fun e he => D.mem_usedArrowsList_of_mem_term ht (Or.inl he)⟩

/-- The base vertex of a relator occurring in the datum, as a vertex of the span. -/
def spanBase (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) : SpanVertex D :=
  ⟨P.base i.1, mem_visitedList_base_of_usedRelator i.2⟩

/-- The relator of `P` occurring in the datum, as a closed path of the span. -/
noncomputable def spanPath (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) :
    Quiver.Path (spanBase D i) (spanBase D i) :=
  pathToSpan D (P.base i.1) (mem_visitedList_base_of_usedRelator i.2) (P.path i.1)
    (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)

/-- The code of an unoriented edge of the span: inherited from `P`. -/
def spanEdgeOf (D : Datum P v n) : Quiver.Total (SpanVertex D) → P.α :=
  fun f => P.edgeOf f.hom.1

theorem spanEdgeOf_reverse (D : Datum P v n) (f : Quiver.Total (SpanVertex D)) :
    spanEdgeOf D (Quiver.totalReverse f) = spanEdgeOf D f := by
  show P.edgeOf (Quiver.totalReverse f).hom.1 = P.edgeOf f.hom.1
  rw [show (Quiver.totalReverse f).hom.1 = Quiver.totalReverse f.hom.1 from rfl]
  exact P.edgeOf_reverse f.hom.1

theorem map_spanEdgeOf (D : Datum P v n) (l : List (Quiver.Total (SpanVertex D))) :
    l.map (fun f => (spanEdgeOf D f : WithBot P.α)) =
      (l.map (fun f => f.hom.1)).map (fun e => (P.edgeOf e : WithBot P.α)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; rfl

theorem map_spanEdgeOf_min (D : Datum P v n) (l : List (Quiver.Total (SpanVertex D))) :
    l.map (fun f => (spanEdgeOf D f : WithTop P.α)) =
      (l.map (fun f => f.hom.1)).map (fun e => (P.edgeOf e : WithTop P.α)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; rfl

theorem pathMax_spanPath (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) :
    pathMax (spanEdgeOf D) (spanPath D i) = pathMax P.edgeOf (P.path i.1) := by
  show ((spanPath D i).arrowList.map (fun f => (spanEdgeOf D f : WithBot P.α))).foldr max ⊥ =
    ((P.path i.1).arrowList.map (fun e => (P.edgeOf e : WithBot P.α))).foldr max ⊥
  rw [map_spanEdgeOf D]
  rw [show (spanPath D i).arrowList.map (fun f => f.hom.1) = (P.path i.1).arrowList from
    pathToSpan_arrowList D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
      (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)]

theorem pathMin_spanPath (D : Datum P v n) (i : {i : P.ι // UsedRelator D i}) :
    pathMin (spanEdgeOf D) (spanPath D i) = pathMin P.edgeOf (P.path i.1) := by
  show ((spanPath D i).arrowList.map (fun f => (spanEdgeOf D f : WithTop P.α))).foldr min ⊤ =
    ((P.path i.1).arrowList.map (fun e => (P.edgeOf e : WithTop P.α))).foldr min ⊤
  rw [map_spanEdgeOf_min D]
  rw [show (spanPath D i).arrowList.map (fun f => f.hom.1) = (P.path i.1).arrowList from
    pathToSpan_arrowList D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
      (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)]

/-- **Howie's step 1.**  The sub-presentation of `P` spanned by the datum `D`: the graph is the
sub-quiver spanned by the datum (`SpanVertex`), and the relators are the relators of `P` occurring
in the datum, as paths of the span. -/
noncomputable def spanPresentation (D : Datum P v n) : Presentation (SpanVertex D) where
  α := P.α
  linearOrder := P.linearOrder
  edgeOf := spanEdgeOf D
  edgeOf_reverse := spanEdgeOf_reverse D
  noSelfLoop := span_noSelfLoop D
  ι := {i : P.ι // UsedRelator D i}
  linearOrder_ι := inferInstance
  base := spanBase D
  path := spanPath D
  reduced := fun i => by
    have h1 : erase D (spanBase D i) (spanPath D i) = P.path i.1 :=
      erase_pathToSpan D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
        (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)
    refine (erase_isReduced D (spanPath D i)).mp ?_
    rw [h1]
    exact P.reduced i.1
  cyclicallyReduced := fun i => by
    have h1 : erase D (spanBase D i) (spanPath D i) = P.path i.1 :=
      erase_pathToSpan D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
        (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)
    have hcomp : ((spanPath D i).comp (spanPath D i)).IsReduced := by
      refine (erase_isReduced D _).mp ?_
      rw [erase_comp]
      rw [h1]
      exact (isReduced_comp_self_iff).mpr ⟨P.reduced i.1, P.cyclicallyReduced i.1,
        fun f _ => P.noSelfLoop (P.base i.1) f⟩
    exact (isReduced_comp_self_iff.mp hcomp).2.1
  notProperPower := fun i => by
    have h1 : erase D (spanBase D i) (spanPath D i) = P.path i.1 :=
      erase_pathToSpan D (P.path i.1) (mem_visitedList_base_of_usedRelator i.2)
        (mem_visitedList_base_of_usedRelator i.2) (inSpan_relator i.2)
    rintro ⟨q, m, hm, heq⟩
    refine P.notProperPower i.1 ⟨erase D (spanBase D i) q, m, hm, ?_⟩
    have h2 : erase D (spanBase D i) (Quiver.Path.compPower q m) =
        Quiver.Path.compPower (erase D (spanBase D i) q) m :=
      erase_compPower D q m
    rw [← h1, heq, h2]
    rfl
  staggered := fun i j hij => by
    refine ⟨?_, ?_⟩
    · rw [pathMax_spanPath, pathMax_spanPath]
      exact (P.staggered i.1 j.1 hij).1
    · rw [pathMin_spanPath, pathMin_spanPath]
      exact (P.staggered i.1 j.1 hij).2

end Work.ORLocInd.Howie
