/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The parity of the visits of a face (G3b): auxiliary data

`Work.ORDunwoody.even_visits_of_label` states that the number of visits of the boundary walk of a
face of `Λ''` whose label is a *fixed* edge `e` of `T` is even.  The proof is the classical one:
the boundary walk of the face maps to a closed walk in the tree `T`, whose edge list is exactly the
list of labels of the visits (`faceLabels`), and a closed walk in a forest crosses every edge an
even number of times (`Work.ORDunwoody.Tracks.even_edges_count`).

This file contains the *data* that the proof is carried out with, and none of the mathematics:

* `DStep D` — a **directed step** of the boundary walk: the traversal of a cell of `Λ'` in one of
  its two directions (visiting the cell's pattern point), or the traversal of a *collapsed*
  generator edge (`L (j,true) = 0`), which visits no pattern point.  (The undirected `Step` of
  `Dunwoody/Source.lean` cannot be used: the boundary walk traverses a cell of a negative letter
  from its target end to its source end, and it is the *direction* that decides which old vertex
  follows the pattern point.)
* `posSteps`, `negSteps`, `faceSteps` — the steps of the boundary walk of a word, in the same
  recursion as `faceAux` (`Dunwoody/FaceWalk.lean`), so that
  `faceAux D a w = (faceSteps D a w).flatMap DStep.verts`
  (and hence the visits of the walk are the pattern points of the steps).
* `geomWalk`, `cellWalk`, `tWalkAux` — the **walk in `T`** obtained by reading the word: each
  cell of `Λ'` traverses the edge of `T` that it maps onto, and a collapsed generator edge does not
  move at all (`colour` of its two ends agree, `Work.ORDunwoody.colour_collapsed`).

The map `colour : BaseV D → V` of `Dunwoody/Pattern.lean` is the map of old vertices to `T`; the
label of a cell is the edge between the colours of its two ends
(`Work.ORDunwoody.cell_label_eq_colour`), so the edge list of `tWalkAux` is the list of labels of
the visits.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Pattern
import Submission.Work.ORDunwoody.colour_collapsed
import Submission.Work.ORDunwoody.cell_label_eq_colour
import Submission.Work.ORDunwoody.faceWalk_getLast

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}

/-! ## The two ends of a cell are adjacent in `T` -/

/-- Counting, as a filtered length, the entries of a list whose image under `f` is a given value. -/
theorem length_filter_eq_count_map {X Y : Type u} [DecidableEq Y] (l : List X) (f : X → Y)
    (e : Y) : (l.filter (fun m => f m = e)).length = (l.map f).count e := by
  rw [← List.countP_eq_length_filter, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro x _
  simp [beq_iff_eq]

/-- The two old vertices at the ends of a cell map to the two ends of an edge of `T`. -/
theorem cell_adj {D : GeoData T t₀ P} (e : Cell D) :
    T.graph.Adj (colour D e.src) (colour D e.tgt) := by
  have h := Cell.label_mem_edgeSet e
  rw [Work.ORDunwoody.cell_label_eq_colour e] at h
  exact (SimpleGraph.mem_edgeSet T.graph).mp h

/-! ## The directed steps of a boundary walk -/

/-- A **directed step** of a boundary walk of `Λ''`: the traversal of a cell (visiting its pattern
point), in the forward direction (`fwd`: source to target) or the backward direction (`bwd`:
target to source), or the traversal of a collapsed generator edge (`skip`, which visits no pattern
point). -/
inductive DStep (D : GeoData T t₀ P) : Type u where
  /-- The traversal of a cell from its source end to its target end. -/
  | fwd (e : Cell D) : DStep D
  /-- The traversal of a cell from its target end to its source end. -/
  | bwd (e : Cell D) : DStep D
  /-- The traversal of a collapsed generator edge. -/
  | skip (u w : BaseV D) : DStep D

namespace DStep

variable {D : GeoData T t₀ P}

/-- The old vertex at which a directed step starts. -/
def src : DStep D → BaseV D
  | fwd e => e.src
  | bwd e => e.tgt
  | skip u _ => u

/-- The old vertex at which a directed step ends. -/
def tgt : DStep D → BaseV D
  | fwd e => e.tgt
  | bwd e => e.src
  | skip _ w => w

/-- The pattern point visited by a directed step, if any. -/
def mid? : DStep D → Option (MidV D)
  | fwd e => some e.mid
  | bwd e => some e.mid
  | skip _ _ => none

/-- The edge of `T` traversed by a directed step, if any. -/
def edge? : DStep D → Option (Sym2 V)
  | fwd e => some e.label
  | bwd e => some e.label
  | skip _ _ => none

/-- The vertices of `Λ''` visited by a directed step, *after* its starting vertex. -/
def verts : DStep D → List (Vertex D)
  | fwd e => [Sum.inr e.mid, Sum.inl e.tgt]
  | bwd e => [Sum.inr e.mid, Sum.inl e.src]
  | skip _ w => [Sum.inl w]

@[simp] theorem src_fwd (e : Cell D) : (fwd e).src = e.src := rfl
@[simp] theorem src_bwd (e : Cell D) : (bwd e).src = e.tgt := rfl
@[simp] theorem src_skip (u w : BaseV D) : (skip u w).src = u := rfl
@[simp] theorem tgt_fwd (e : Cell D) : (fwd e).tgt = e.tgt := rfl
@[simp] theorem tgt_bwd (e : Cell D) : (bwd e).tgt = e.src := rfl
@[simp] theorem tgt_skip (u w : BaseV D) : (skip u w).tgt = w := rfl
@[simp] theorem mid?_fwd (e : Cell D) : (fwd e).mid? = some e.mid := rfl
@[simp] theorem mid?_bwd (e : Cell D) : (bwd e).mid? = some e.mid := rfl
@[simp] theorem mid?_skip (u w : BaseV D) : (skip u w).mid? = none := rfl
@[simp] theorem edge?_fwd (e : Cell D) : (fwd e).edge? = some e.label := rfl
@[simp] theorem edge?_bwd (e : Cell D) : (bwd e).edge? = some e.label := rfl
@[simp] theorem edge?_skip (u w : BaseV D) : (skip u w).edge? = none := rfl
@[simp] theorem verts_fwd (e : Cell D) : (fwd e).verts = [Sum.inr e.mid, Sum.inl e.tgt] := rfl
@[simp] theorem verts_bwd (e : Cell D) : (bwd e).verts = [Sum.inr e.mid, Sum.inl e.src] := rfl
@[simp] theorem verts_skip (u w : BaseV D) : (skip u w).verts = [Sum.inl w] := rfl

/-- The pattern point of a step is the one visited by its vertex list. -/
theorem filterMap_midOf_verts (s : DStep D) :
    (s.verts).filterMap Vertex.midOf = (s.mid?).toList := by
  cases s <;> rfl

/-- The label of the pattern point of a step is the edge it traverses. -/
theorem map_label_mid? (s : DStep D) :
    (s.mid?).map (MidV.label (D := D)) = s.edge? := by
  cases s <;> rfl

end DStep

/-! ## The steps of a boundary walk -/

/-- The steps of the traversal of the positive letter `(j,true)` based at `a`, in order. -/
def posSteps (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (DStep D) :=
  if h : D.L (j, true) = 0 then
    [DStep.skip ((a, Sum.inl ()) : BaseV D)
      ((a * CayV.genE P (j, true), Sum.inl ()) : BaseV D)]
  else (List.finRange (D.L (j, true))).map (fun k => DStep.fwd (⟨a, j, k⟩ : Cell D))

/-- The steps of the traversal of the negative letter `(j,false)` based at `a` (i.e. of the reverse
of the positive generator edge based at `a * (genE (j,true))⁻¹`), in order. -/
def negSteps (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (DStep D) :=
  let a' := a * (CayV.genE P (j, true))⁻¹
  if h : D.L (j, true) = 0 then
    [DStep.skip ((a, Sum.inl ()) : BaseV D) ((a', Sum.inl ()) : BaseV D)]
  else ((List.finRange (D.L (j, true))).reverse).map (fun k => DStep.bwd (⟨a', j, k⟩ : Cell D))

/-- **The steps of the boundary walk of a word**, in the order in which the walk traverses them.
This is the companion of `faceAux`: `faceAux D a w = (faceSteps D a w).flatMap DStep.verts`. -/
def faceSteps (D : GeoData T t₀ P) (a : G) : List (Fin P.n × Bool) → List (DStep D)
  | [] => []
  | (j, true) :: w => posSteps D a j ++ faceSteps D (a * CayV.genE P (j, true)) w
  | (j, false) :: w => negSteps D a j ++ faceSteps D (a * (CayV.genE P (j, true))⁻¹) w

@[simp] theorem faceSteps_nil (D : GeoData T t₀ P) (a : G) :
    faceSteps D a [] = [] := rfl

@[simp] theorem faceSteps_true (D : GeoData T t₀ P) (a : G) (j : Fin P.n)
    (w : List (Fin P.n × Bool)) :
    faceSteps D a ((j, true) :: w) =
      posSteps D a j ++ faceSteps D (a * CayV.genE P (j, true)) w := rfl

@[simp] theorem faceSteps_false (D : GeoData T t₀ P) (a : G) (j : Fin P.n)
    (w : List (Fin P.n × Bool)) :
    faceSteps D a ((j, false) :: w) =
      negSteps D a j ++ faceSteps D (a * (CayV.genE P (j, true))⁻¹) w := rfl

/-! ## The walk in `T` -/

/-- The walk in `T` that traverses the cells of the positive generator edge `(j,true)` based at `a`
(in order): it runs along the geodesic of that generator, translated by `a`. -/
def cellWalk (D : GeoData T t₀ P) (a : G) (j : Fin P.n) :
    (n : ℕ) → n ≤ D.L (j, true) →
      T.graph.Walk (colour D (pos D a j 0)) (colour D (pos D a j n))
  | 0, _ => SimpleGraph.Walk.nil
  | n + 1, h =>
      (cellWalk D a j n (Nat.le_of_lt h)).append
        (SimpleGraph.Walk.cons (cell_adj (⟨a, j, ⟨n, h⟩⟩ : Cell D)) SimpleGraph.Walk.nil)

/-- The walk in `T` that traverses the cells of the positive generator edge `(j,true)` based at `a`.
For a collapsed generator (`L (j,true) = 0`) it is a single point. -/
def geomWalk (D : GeoData T t₀ P) (a : G) (j : Fin P.n) :
    T.graph.Walk (colour D ((a, Sum.inl ()) : BaseV D))
      (colour D (((a * CayV.genE P (j, true)), Sum.inl ()) : BaseV D)) :=
  if h : D.L (j, true) = 0 then
    (SimpleGraph.Walk.nil (G := T.graph) (u := colour D ((a, Sum.inl ()) : BaseV D))).copy rfl
      (Work.ORDunwoody.colour_collapsed a j h)
  else
    (cellWalk D a j (D.L (j, true)) le_rfl).copy (congrArg (colour D) (pos_zero D a j)) (by
      have h1 : pos D a j (D.L (j, true)) =
          (((a * CayV.genE P (j, true)), Sum.inl ()) : BaseV D) := by
        have := pos_succ_of_not_lt D a j (i := D.L (j, true) - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ D.L (j, true))] at this
      exact congrArg (colour D) h1)

/-- **The walk in `T` associated with reading the word `w` at `a`**: it reads the word letter by
letter, traversing along the geodesic of each generator, and returns the `colour` of the current
base point. -/
def tWalkAux (D : GeoData T t₀ P) : (a : G) → (w : List (Fin P.n × Bool)) →
    T.graph.Walk (colour D ((a, Sum.inl ()) : BaseV D))
      (colour D ((endPt P a w, Sum.inl ()) : BaseV D))
  | a, [] => SimpleGraph.Walk.nil
  | a, (j, true) :: w =>
      (geomWalk D a j).append (tWalkAux D (a * CayV.genE P (j, true)) w)
  | a, (j, false) :: w =>
      (((geomWalk D (a * (CayV.genE P (j, true))⁻¹) j).reverse.copy
          (congrArg (fun x => colour D ((x, Sum.inl ()) : BaseV D)) (by group)) rfl).append
        (tWalkAux D (a * (CayV.genE P (j, true))⁻¹) w)).copy rfl
        (congrArg (fun x => colour D ((x, Sum.inl ()) : BaseV D))
          (Work.ORDunwoody.endPt_false_eq a j w).symm)

@[simp] theorem tWalkAux_nil (D : GeoData T t₀ P) (a : G) :
    tWalkAux D a [] = SimpleGraph.Walk.nil := rfl

@[simp] theorem tWalkAux_true (D : GeoData T t₀ P) (a : G) (j : Fin P.n)
    (w : List (Fin P.n × Bool)) :
    tWalkAux D a ((j, true) :: w) =
      (geomWalk D a j).append (tWalkAux D (a * CayV.genE P (j, true)) w) := rfl

end Work.ORDunwoody.Dunwoody
