/-
# Every vertex of the span of a datum is reachable from its base vertex

Howie's step 1 (the file `Span.lean`) replaces the graph `Γ` by the subgraph spanned by a datum
`∆`: its vertices are the vertices visited by `∆`, and its arrows are the arrows occurring in `∆`
together with their reverses.  This file proves that this subgraph is *connected from the base
vertex*: every vertex visited by the datum is the endpoint of a path of the span starting at
`spanV D = v`.

The mathematical content is that each of the paths making up the datum (`γ_j`, the `δ_{j,k}` and the
relators `α_{j,k}`) lies in the span, and that a vertex of a path is the endpoint of a *prefix* of
that path, which again lies in the span.  The three cases of `visitedList` are:

* the base vertex `v` itself, joined to itself by the trivial path;
* a vertex of `γ_j`, reachable from `v` along the prefix of `γ_j`;
* a vertex of the `δ_{j,k}` or of `α_{j,k}`; in the second case one first walks from `v` to the base
  vertex of the relator along `δ_{j,k}` and then along the prefix of the relator.

Target statement: `Work.ORLocInd.Howie.span_reachable`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.exists_spanDatum
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.Span

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Quiver.Path

variable {V : Type u} [Quiver V]

/-- The arrow list of a composite path is the concatenation of the arrow lists. -/
theorem arrowList_comp {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (p.comp q).arrowList = p.arrowList ++ q.arrowList := by
  induction q with
  | nil => simp
  | cons q' e ih =>
    rw [Quiver.Path.comp_cons, Quiver.Path.arrowList_cons, ih, Quiver.Path.arrowList_cons,
      List.append_assoc]

end Quiver.Path

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
variable {P : Presentation V} {v : V} {n : ℕ}

/-- The predicate `InSpan` is inherited by the left factor of a composite path. -/
theorem InSpan.of_comp_left {D : Datum P v n} {a b c : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} (h : InSpan D (p.comp q)) : InSpan D p where
  vertices := fun x hx => h.vertices x (by
    rw [Quiver.Path.vertices_comp]
    have hx' : x ∈ p.vertices.dropLast ++ [b] := by
      have hh := hx
      rw [← Quiver.Path.dropLast_append_end_eq p] at hh
      exact hh
    rcases List.mem_append.mp hx' with hd | he
    · exact List.mem_append_left _ hd
    · exact List.mem_append_right _ (List.mem_singleton.mp he ▸ Quiver.Path.start_mem_vertices q))
  arrows := fun e he => h.arrows e (by
    rw [Quiver.Path.arrowList_comp]
    exact List.mem_append_left _ he)

/-- Every vertex of a path lying in the span is the endpoint of a prefix of that path which also
lies in the span. -/
theorem exists_prefix_inSpan {D : Datum P v n} {a b : V} {p : Quiver.Path a b}
    (hp : InSpan D p) {x : V} (hx : x ∈ p.vertices) :
    ∃ q : Quiver.Path a x, InSpan D q := by
  obtain ⟨p₁, p₂, hp₁⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hx
  exact ⟨p₁, InSpan.of_comp_left (p := p₁) (q := p₂) (hp₁ ▸ hp)⟩

theorem span_reachable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {P : Work.ORLocInd.Howie.Presentation V} {v : V} {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n) :
    ∀ x : Work.ORLocInd.Howie.SpanVertex D,
      Nonempty (Quiver.Path (Work.ORLocInd.Howie.spanV D) x) := by
  intro x
  obtain ⟨y, hy⟩ := x
  have hy' : y ∈ [v] ++ (List.finRange n).flatMap (fun j => (D.γ j).1.vertices) ++
      (List.finRange n).flatMap (fun j =>
        (D.terms j).flatMap RelatorTerm.visitedList) := hy
  rcases List.mem_append.mp hy' with hy' | hy'
  · rcases List.mem_append.mp hy' with hy' | hy'
    · -- the base vertex `v` itself
      rw [List.mem_singleton] at hy'
      subst hy'
      exact ⟨Quiver.Path.cast rfl (Subtype.ext rfl)
        (Quiver.Path.nil : Quiver.Path (spanV D) (spanV D))⟩
    · -- a vertex of a closed path `γ_j`
      rcases List.mem_flatMap.mp hy' with ⟨j, -, hj⟩
      obtain ⟨q, hq⟩ := exists_prefix_inSpan (inSpan_gamma D j) hj
      exact ⟨pathToSpan D v D.mem_visitedList_base q hy hq⟩
  · rcases List.mem_flatMap.mp hy' with ⟨j, -, hj⟩
    rcases List.mem_flatMap.mp hj with ⟨t, ht, htj⟩
    rw [RelatorTerm.visitedList] at htj
    rcases List.mem_append.mp htj with htj | htj
    · -- a vertex of the path `δ` of a term
      obtain ⟨q, hq⟩ := exists_prefix_inSpan (inSpan_delta D ht) htj
      exact ⟨pathToSpan D v D.mem_visitedList_base q hy hq⟩
    · -- a vertex of the relator path of a term: walk to its base vertex along `δ`
      have hw : P.base t.i ∈ D.visitedList :=
        mem_visitedList_base_of_usedRelator (usedRelator_of_mem_terms ht)
      obtain ⟨q, hq⟩ := exists_prefix_inSpan (inSpan_relator (usedRelator_of_mem_terms ht)) htj
      exact ⟨(pathToSpan D v D.mem_visitedList_base t.δ hw (inSpan_delta D ht)).comp
        (pathToSpan D (P.base t.i) hw q hy hq)⟩

end Work.ORLocInd.Howie
