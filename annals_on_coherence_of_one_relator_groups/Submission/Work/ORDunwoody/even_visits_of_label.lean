import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk
import Submission.Work.ORDunwoody.Tracks.even_edges_count
import Submission.Work.ORDunwoody.faceWalk_getLast
import Submission.Work.ORDunwoody.even_visits_defs
import Submission.Work.ORDunwoody.faceVisits_eq_faceAux
import Submission.Work.ORDunwoody.faceAux_eq_faceSteps
import Submission.Work.ORDunwoody.tWalkAux_edges

namespace Work.ORDunwoody

universe u

open Work.ORDunwoody.Dunwoody

/--
**Parity of the visits of a face** (step (G3b) of the Dunwoody construction).

The boundary walk of the face `(r, c)` of `Λ''` maps, under `colour`, to a closed walk in the tree
`T` — the walk `tWalkAux` that reads the word `toWord r` at `c`, traversing along the geodesic of
each generator and staying put on a collapsed generator.  Its edge list is exactly the list of
labels of the visits of the face (`faceLabels`), and a closed walk in a forest crosses each of its
edges an even number of times (`Work.ORDunwoody.Tracks.even_edges_count`).  Hence every edge `e`
of `T` is the label of an even number of visits of the face.
-/
theorem even_visits_of_label {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (r : {r : FreeGroup (Fin P.n) // r ∈ P.rel}) (c : G) (e : Sym2 V) :
    Even ((Work.ORDunwoody.Dunwoody.faceVisits D c (FreeGroup.toWord r.1)).filter
      (fun m => m.label = e)).length := by
  -- the visits of the face are the pattern points of the steps of the walk
  have hFV : faceVisits D c (FreeGroup.toWord r.1) =
      (faceSteps D c (FreeGroup.toWord r.1)).filterMap DStep.mid? := by
    rw [faceVisits_eq_faceAux, faceAux_eq_faceSteps]
  -- the labels of the visits are the edges traversed by the directions of the walk
  have hFL : faceLabels D c (FreeGroup.toWord r.1) =
      (faceSteps D c (FreeGroup.toWord r.1)).filterMap DStep.edge? := by
    unfold faceLabels
    rw [hFV, List.map_filterMap]
    simp only [DStep.map_label_mid?]
  have hwalk : (tWalkAux D c (FreeGroup.toWord r.1)).edges =
      faceLabels D c (FreeGroup.toWord r.1) := by
    rw [hFL, tWalkAux_edges]
  -- the walk in `T` is closed: reading a defining relator returns to the base point
  have hclosed : endPt P c (FreeGroup.toWord r.1) = c := endPt_toWord_eq P r.2 c
  have heven : Even ((tWalkAux D c (FreeGroup.toWord r.1)).edges.count e) := by
    have h := Tracks.even_edges_count T.graph T.isTree.isAcyclic
      ((tWalkAux D c (FreeGroup.toWord r.1)).copy rfl
        (congrArg (fun x => colour D ((x, Sum.inl ()) : BaseV D)) hclosed)) e
    rwa [SimpleGraph.Walk.edges_copy] at h
  -- the filtered length of the visits is the multiplicity of `e` in the edge list
  have hgoal : ((faceVisits D c (FreeGroup.toWord r.1)).filter
        (fun m => m.label = e)).length
      = (tWalkAux D c (FreeGroup.toWord r.1)).edges.count e := by
    rw [hFV, length_filter_eq_count_map (f := fun m : MidV D => m.label), List.map_filterMap]
    simp only [DStep.map_label_mid?]
    rw [← hFL, ← hwalk]
  rw [hgoal]
  exact heven

end Work.ORDunwoody
