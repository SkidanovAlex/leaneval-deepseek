import Mathlib
import Submission.Work.ORDunwoody.even_visits_defs
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-! ## The two descriptions of a boundary walk

`faceAux` (the list of vertices visited) and `faceSteps` (the list of directed steps taken) are the
two descriptions of the boundary walk of a face of `Λ''`.  The visits of the walk are the pattern
points; a vertex list and a step list give the same visits when each step contributes exactly its
own pattern point.
-/

/-- A general list identity: filtering the result of a `flatMap` is the same as `flatMap`ping the
filtered blocks. -/
theorem w_flatMap_toList_eq_filterMap {α β : Type*} (l : List α) (o : α → Option β) :
    l.flatMap (fun a => (o a).toList) = l.filterMap o := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons, List.filterMap_cons]
      cases o a <;> simp [ih]

/-- Traversing the positive letter `(j,true)` visits the pattern points of the steps `posSteps`. -/
theorem edgeTailPos_eq_flatMap_verts (a : G) (j : Fin P.n) :
    Work.ORDunwoody.Dunwoody.edgeTailPos D a j =
      (Work.ORDunwoody.Dunwoody.posSteps D a j).flatMap Work.ORDunwoody.Dunwoody.DStep.verts := by
  unfold Work.ORDunwoody.Dunwoody.edgeTailPos Work.ORDunwoody.Dunwoody.posSteps
  by_cases h : D.L (j, true) = 0
  · simp [h]
  · simp only [h, dif_neg, not_false_eq_true, if_neg]
    rw [List.flatMap_map]
    exact List.flatMap_congr
      (fun k _ => by
        simp [Work.ORDunwoody.Dunwoody.DStep.verts, Work.ORDunwoody.Dunwoody.Cell.mid,
          Work.ORDunwoody.Dunwoody.Cell.tgt])

/-- Traversing the negative letter `(j,false)` visits the pattern points of the steps `negSteps`. -/
theorem edgeTailNeg_eq_flatMap_verts (a : G) (j : Fin P.n) :
    Work.ORDunwoody.Dunwoody.edgeTailNeg D a j =
      (Work.ORDunwoody.Dunwoody.negSteps D a j).flatMap Work.ORDunwoody.Dunwoody.DStep.verts := by
  unfold Work.ORDunwoody.Dunwoody.edgeTailNeg Work.ORDunwoody.Dunwoody.negSteps
  by_cases h : D.L (j, true) = 0
  · simp [h]
  · simp only [h, dif_neg, not_false_eq_true, if_neg]
    rw [List.flatMap_map]
    exact List.flatMap_congr
      (fun k _ => by
        simp [Work.ORDunwoody.Dunwoody.DStep.verts, Work.ORDunwoody.Dunwoody.Cell.mid,
          Work.ORDunwoody.Dunwoody.Cell.src])

/-- The vertices of the boundary walk of a word are the vertices visited by its directed steps. -/
theorem faceAux_eq_flatMap_verts (a : G) (w : List (Fin P.n × Bool)) :
    Work.ORDunwoody.Dunwoody.faceAux D a w =
      (Work.ORDunwoody.Dunwoody.faceSteps D a w).flatMap Work.ORDunwoody.Dunwoody.DStep.verts := by
  induction w generalizing a with
  | nil => rfl
  | cons x w ih =>
      obtain ⟨j, b⟩ := x
      cases b
      case false =>
        rw [Work.ORDunwoody.Dunwoody.faceAux_false, Work.ORDunwoody.Dunwoody.faceSteps_false,
          List.flatMap_append, ih, edgeTailNeg_eq_flatMap_verts]
      case true =>
        rw [Work.ORDunwoody.Dunwoody.faceAux_true, Work.ORDunwoody.Dunwoody.faceSteps_true,
          List.flatMap_append, ih, edgeTailPos_eq_flatMap_verts]

theorem faceAux_eq_faceSteps {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (w : List (Fin P.n × Bool)) :
    (Work.ORDunwoody.Dunwoody.faceAux D a w).filterMap Work.ORDunwoody.Dunwoody.Vertex.midOf =
      (Work.ORDunwoody.Dunwoody.faceSteps D a w).filterMap Work.ORDunwoody.Dunwoody.DStep.mid? := by
  rw [faceAux_eq_flatMap_verts, List.filterMap_flatMap]
  rw [show (Work.ORDunwoody.Dunwoody.faceSteps D a w).flatMap
          (fun s => (Work.ORDunwoody.Dunwoody.DStep.verts s).filterMap
            Work.ORDunwoody.Dunwoody.Vertex.midOf) =
        (Work.ORDunwoody.Dunwoody.faceSteps D a w).flatMap
          (fun s => (Work.ORDunwoody.Dunwoody.DStep.mid? s).toList) from
      List.flatMap_congr
        (fun s _ => Work.ORDunwoody.Dunwoody.DStep.filterMap_midOf_verts s)]
  exact w_flatMap_toList_eq_filterMap _ _

end Work.ORDunwoody
