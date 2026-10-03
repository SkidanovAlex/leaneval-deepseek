/-
# The subgraph spanned by a datum (Howie 2000, step 1 of the proof of Theorem 3.1)

Howie's first step in the proof of Theorem 3.1 is

> The first step is to replace `Γ` by the smallest subgraph `Γ₀` containing all the paths `δ_{j,k}`
> and `α_{j,k}` (and hence all the `γ_j`), and `R` by the subset `R₀ = {α_{j,k}}`. [...] the
> presentation of `G₀` is staggered under the restriction of the orders [...] In particular, if we
> prove that `H₀ = {1}`, then it follows that `H = {1}`.

This file sets up the *combinatorial* part of that reduction: given a datum `D` in a presentation
`P`, the graph spanned by `D` is the sub-quiver of `Γ` whose

* vertices are the vertices visited by `D` (the list `D.visitedList` of `Datum.lean`), and
* arrows are the arrows occurring in the paths of `D`, together with their reverses, as a subtype
  of `Quiver.Total V`.

Concretely, `SpanVertex D = {x : V // x ∈ D.visitedList}` with
`SpanArrow D u w = {e : Quiver.Total V // e.left = u.val ∧ e.right = w.val ∧ e ∈ D.usedArrowsList}`,
together with the `Quiver` and `Quiver.HasInvolutiveReverse` instances.

We also provide

* `InSpan D p`: the predicate "all vertices of `p` are visited by `D` and all its arrows occur in
  `D`", and `pathToSpan`: such a path of `Γ` *is* a path of the span;
* `erase`: the erasure of a path of the span to a path of `Γ`, with `erase_pathToSpan`.

The `Presentation` structure of the span itself, the transport of a datum to the span, and the
transfer of the vanishing statement along the inclusion are built on top of this file.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Datum

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]

/-! ## Paths and their vertex lists -/

section PathLists

variable {a b c : V}

/-- The endpoint of a path is one of its vertices. -/
theorem Quiver.Path.mem_vertices_endpoint (p : Quiver.Path a b) : b ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [Quiver.Path.vertices_cons, List.concat_eq_append]
      exact List.mem_append.mpr (Or.inr (by simp))

/-- The initial vertex of a path is one of its vertices. -/
theorem Quiver.Path.mem_vertices_head (p : Quiver.Path a b) : a ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [Quiver.Path.vertices_cons, List.concat_eq_append]
      exact List.mem_append.mpr (Or.inl ih)

theorem Quiver.Path.mem_vertices_cons_of_mem {p : Quiver.Path a b} (e : b ⟶ c) {x : V}
    (h : x ∈ p.vertices) : x ∈ (p.cons e).vertices := by
  rw [Quiver.Path.vertices_cons, List.concat_eq_append]
  exact List.mem_append.mpr (Or.inl h)

theorem Quiver.Path.mem_arrowList_cons_of_mem {p : Quiver.Path a b} (e : b ⟶ c)
    {f : Quiver.Total V} (h : f ∈ p.arrowList) : f ∈ (p.cons e).arrowList := by
  rw [Quiver.Path.arrowList_cons]
  exact List.mem_append.mpr (Or.inl h)

theorem Quiver.Path.mem_arrowList_cons_self (p : Quiver.Path a b) (e : b ⟶ c) :
    Quiver.Total.mk b c e ∈ (p.cons e).arrowList := by
  rw [Quiver.Path.arrowList_cons]
  exact List.mem_append.mpr (Or.inr (by simp))

end PathLists

namespace Datum

variable {P : Presentation V} {v : V} {n : ℕ}

/-- The arrows occurring in the paths of a datum: those of the `γ_j`, and those of the paths `δ`
and relator paths of its terms. -/
noncomputable def rawArrows (D : Datum P v n) : List (Quiver.Total V) :=
  (List.finRange n).flatMap (fun j => (D.γ j).1.arrowList) ++
    (List.finRange n).flatMap (fun j =>
      (D.terms j).flatMap (fun t => t.δ.arrowList ++ (P.path t.i).arrowList))

/-- The arrows occurring in a datum, together with the reverses of those arrows: the arrow set of
the subgraph spanned by the datum.

(There is deliberately no `dedup` here: the arrow set of the span is the *subtype* of
`Quiver.Total V` determined by this list, so repetitions are harmless.) -/
noncomputable def usedArrowsList (D : Datum P v n) : List (Quiver.Total V) :=
  D.rawArrows ++ D.rawArrows.map Quiver.totalReverse

theorem mem_usedArrowsList_iff (D : Datum P v n) (e : Quiver.Total V) :
    e ∈ D.usedArrowsList ↔ e ∈ D.rawArrows ∨ Quiver.totalReverse e ∈ D.rawArrows := by
  rw [usedArrowsList, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨x, hx, hxe⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [← hxe, Quiver.totalReverse_involutive]; exact hx)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨Quiver.totalReverse e, h, Quiver.totalReverse_involutive e⟩

theorem totalReverse_mem_usedArrowsList (D : Datum P v n) {e : Quiver.Total V}
    (h : e ∈ D.usedArrowsList) : Quiver.totalReverse e ∈ D.usedArrowsList := by
  rw [mem_usedArrowsList_iff] at h ⊢
  rcases h with h | h
  · exact Or.inr (by rwa [Quiver.totalReverse_involutive])
  · exact Or.inl h

theorem mem_usedArrowsList_of_mem_gamma (D : Datum P v n) (j : Fin n) {e : Quiver.Total V}
    (h : e ∈ (D.γ j).1.arrowList) : e ∈ D.usedArrowsList := by
  show e ∈ D.rawArrows ++ D.rawArrows.map Quiver.totalReverse
  refine List.mem_append.mpr (Or.inl ?_)
  show e ∈ (List.finRange n).flatMap (fun j => (D.γ j).1.arrowList) ++
    (List.finRange n).flatMap (fun j =>
      (D.terms j).flatMap (fun t => t.δ.arrowList ++ (P.path t.i).arrowList))
  exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, h⟩))

theorem mem_usedArrowsList_of_mem_term (D : Datum P v n) {j : Fin n} {t : RelatorTerm P v}
    (ht : t ∈ D.terms j) {e : Quiver.Total V}
    (h : e ∈ t.δ.arrowList ∨ e ∈ (P.path t.i).arrowList) : e ∈ D.usedArrowsList := by
  show e ∈ D.rawArrows ++ D.rawArrows.map Quiver.totalReverse
  refine List.mem_append.mpr (Or.inl ?_)
  show e ∈ (List.finRange n).flatMap (fun j => (D.γ j).1.arrowList) ++
    (List.finRange n).flatMap (fun j =>
      (D.terms j).flatMap (fun t => t.δ.arrowList ++ (P.path t.i).arrowList))
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j, List.mem_flatMap.mpr ⟨t, ht,
    List.mem_append.mpr h⟩⟩

theorem mem_visitedList_of_mem_gamma (D : Datum P v n) (j : Fin n) {x : V}
    (h : x ∈ (D.γ j).1.vertices) : x ∈ D.visitedList := by
  show x ∈ [v] ++ (List.finRange n).flatMap (fun j => (D.γ j).1.vertices) ++
    (List.finRange n).flatMap (fun j => (D.terms j).flatMap RelatorTerm.visitedList)
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
  exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j, h⟩

theorem mem_visitedList_of_mem_term (D : Datum P v n) {j : Fin n} {t : RelatorTerm P v}
    (ht : t ∈ D.terms j) {x : V} (h : x ∈ t.visitedList) : x ∈ D.visitedList := by
  show x ∈ [v] ++ (List.finRange n).flatMap (fun j => (D.γ j).1.vertices) ++
    (List.finRange n).flatMap (fun j => (D.terms j).flatMap RelatorTerm.visitedList)
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
    List.mem_flatMap.mpr ⟨t, ht, h⟩⟩

theorem mem_visitedList_of_mem_term_delta (D : Datum P v n) {j : Fin n} {t : RelatorTerm P v}
    (ht : t ∈ D.terms j) {x : V} (h : x ∈ t.δ.vertices) : x ∈ D.visitedList :=
  mem_visitedList_of_mem_term D ht (by
    rw [RelatorTerm.visitedList]; exact List.mem_append.mpr (Or.inl h))

theorem mem_visitedList_of_mem_term_relator (D : Datum P v n) {j : Fin n} {t : RelatorTerm P v}
    (ht : t ∈ D.terms j) {x : V} (h : x ∈ (P.path t.i).vertices) : x ∈ D.visitedList :=
  mem_visitedList_of_mem_term D ht (by
    rw [RelatorTerm.visitedList]; exact List.mem_append.mpr (Or.inr h))

theorem mem_visitedList_base (D : Datum P v n) : v ∈ D.visitedList := by
  show v ∈ [v] ++ (List.finRange n).flatMap (fun j => (D.γ j).1.vertices) ++
    (List.finRange n).flatMap (fun j => (D.terms j).flatMap RelatorTerm.visitedList)
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (by simp))))

end Datum

/-! ## The span of a datum -/

section Span

variable {P : Presentation V} {v : V} {n : ℕ}

/-- The vertices of the span of a datum: the vertices visited by the datum. -/
abbrev SpanVertex (D : Datum P v n) : Type u := {x : V // x ∈ D.visitedList}

/-- The arrows of the span of a datum: the arrows occurring in the datum, with their reverses, as
arrows between the corresponding vertices of the span. -/
abbrev SpanArrow (D : Datum P v n) (u w : SpanVertex D) : Type u :=
  {e : Quiver.Total V // e.left = u.1 ∧ e.right = w.1 ∧ e ∈ D.usedArrowsList}

instance instQuiverSpanVertex (D : Datum P v n) : Quiver (SpanVertex D) :=
  ⟨fun u w => SpanArrow D u w⟩

instance instReverseSpanVertex (D : Datum P v n) : Quiver.HasInvolutiveReverse (SpanVertex D) where
  reverse' := fun {u w} f =>
    ⟨Quiver.totalReverse f.1, by
      obtain ⟨e, h1, h2, h3⟩ := f
      exact ⟨by simpa using h2, by simpa using h1,
        D.totalReverse_mem_usedArrowsList h3⟩⟩
  inv' := fun {u w} f => Subtype.ext (Quiver.totalReverse_involutive f.1)

/-- A path of the ambient graph lies in the span of a datum when all its vertices are visited by
the datum and all its arrows occur in the datum. -/
structure InSpan (D : Datum P v n) {a b : V} (p : Quiver.Path a b) : Prop where
  /-- all vertices of `p` are visited by the datum -/
  vertices : ∀ x ∈ p.vertices, x ∈ D.visitedList
  /-- all arrows of `p` occur in the datum -/
  arrows : ∀ e ∈ p.arrowList, e ∈ D.usedArrowsList

/-- A path of the ambient graph all of whose arrows occur in the datum and all of whose vertices
are visited by the datum is a path of the span.  The endpoints of the resulting path are the
endpoints of `p` with the membership proofs supplied by the caller; for a *closed* path one passes
the same proof for both endpoints, which makes the resulting path closed. -/
noncomputable def pathToSpan (D : Datum P v n) (a : V) (ha : a ∈ D.visitedList) :
    ∀ {b : V} (p : Quiver.Path a b) (hb : b ∈ D.visitedList) (hp : InSpan D p),
      Quiver.Path (⟨a, ha⟩ : SpanVertex D) ⟨b, hb⟩
  | _, .nil, hb, _ =>
      Quiver.Path.cast rfl (Subtype.ext rfl)
        (Quiver.Path.nil : Quiver.Path (⟨a, ha⟩ : SpanVertex D) ⟨a, ha⟩)
  | _, .cons q e, hb, hp =>
      (pathToSpan D a ha q
        (hp.vertices _ (Quiver.Path.mem_vertices_cons_of_mem e (Quiver.Path.mem_vertices_endpoint q)))
        ⟨fun x hx => hp.vertices x (Quiver.Path.mem_vertices_cons_of_mem e hx),
          fun f hf => hp.arrows f (Quiver.Path.mem_arrowList_cons_of_mem e hf)⟩).cons
        ⟨Quiver.Total.mk _ _ e, rfl, rfl, hp.arrows _ (Quiver.Path.mem_arrowList_cons_self q e)⟩

end Span

/-! ## Erasure: paths of the span are paths of the ambient graph -/

section Erase

variable {P : Presentation V} {v : V} {n : ℕ}

/-- The erasure of a path of the span: its image in the ambient graph. -/
def erase (D : Datum P v n) (u : SpanVertex D) :
    ∀ {w : SpanVertex D}, Quiver.Path u w → Quiver.Path u.1 w.1
  | _, .nil => .nil
  | _, .cons p e => (erase D u p).cons (Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom)

theorem erase_nil (D : Datum P v n) (u : SpanVertex D) :
    erase D u (Quiver.Path.nil : Quiver.Path u u) = Quiver.Path.nil := rfl

theorem erase_cons (D : Datum P v n) {u w x : SpanVertex D} (p : Quiver.Path u w) (e : w ⟶ x) :
    erase D u (p.cons e) = (erase D u p).cons (Quiver.Hom.cast e.2.1 e.2.2.1 e.1.hom) := rfl

end Erase

end Work.ORLocInd.Howie
