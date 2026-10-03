import Mathlib
import Submission.Work.ORDunwoody.even_visits_defs
import Submission.Work.ORDunwoody.Dunwoody.FaceWalk

open scoped Sym2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

/-!
# The edge list of the walk in `T` associated with reading a word

`Work.ORDunwoody.Dunwoody.tWalkAux` reads a word `w` at a group element `a`, traversing along the
geodesic of every generator (in `T`); `Work.ORDunwoody.Dunwoody.faceSteps` records the *directed
steps* of the boundary walk of the corresponding face of `Λ''`, each carrying the label of the
cell it crosses (`DStep.edge?`).  This file proves that the two agree: the edge list of the walk
in `T` is the list of the edges traversed by the steps.

The proof is by induction on the word, and the one nontrivial input is the computation of the
edges of the walk `geomWalk` along a single generator edge (`cellWalk`): those edges are exactly
the labels of the successive cells of the geodesic.
-/

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody
open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-! ## The edges of the walk along a single generator edge -/

/-- **The edge list of `cellWalk`.**  The walk in `T` that traverses the successive cells of the
subdivided generator edge `(j,true)` based at `a` has, as its edge list, the labels of those
cells in order. -/
theorem cellWalk_edges (a : G) (j : Fin P.n) :
    ∀ (n : ℕ) (hn : n ≤ D.L (j, true)),
    (cellWalk D a j n hn).edges =
      (List.finRange n).map (fun k => (⟨a, j, k.castLE hn⟩ : Cell D).label) := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
      intro hn
      -- the last cell of the geodesic contributes the last edge
      have hlast : s(colour D (pos D a j n),
            colour D ({c := a, j := j, k := ⟨n, hn⟩} : Cell D).tgt)
          = (⟨a, j, (Fin.last n).castLE hn⟩ : Cell D).label := by
        rw [cell_label_eq_colour]
        congr 1
      simp only [cellWalk, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.edges_nil]
      rw [ih (Nat.le_of_lt hn)]
      rw [List.finRange_succ_last, List.map_append, List.map_map, List.map_singleton]
      rw [hlast]
      congr 1

/-- **The edge list of `geomWalk`.**  The walk along the (possibly collapsed) generator edge
`(j,true)` based at `a` has the same edge list as the labels of the steps `posSteps`. -/
theorem geomWalk_edges (a : G) (j : Fin P.n) :
    (geomWalk D a j).edges = (posSteps D a j).filterMap DStep.edge? := by
  by_cases h : D.L (j, true) = 0
  · -- a collapsed generator edge moves nowhere and visits no pattern point
    simp only [geomWalk, posSteps, dif_pos h, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_nil, List.filterMap_cons, DStep.edge?_skip, List.filterMap_nil]
  · simp only [geomWalk, posSteps, dif_neg h, SimpleGraph.Walk.edges_copy]
    rw [cellWalk_edges a j (D.L (j, true)) le_rfl]
    simp only [List.filterMap_map, DStep.edge?_fwd, Function.comp_apply, Fin.castLE_rfl]
    rw [← List.filterMap_eq_map]
    rfl

/-- **The edge list of `negSteps`.**  The steps of the traversal of the reverse of the generator
edge `(j,true)` based at `a` produce the labels of the cells of the geodesic at
`a * (genE (j,true))⁻¹`, in reverse order. -/
theorem negSteps_edges (a : G) (j : Fin P.n) :
    (negSteps D a j).filterMap DStep.edge? =
      (geomWalk D (a * (CayV.genE P (j, true))⁻¹) j).edges.reverse := by
  by_cases h : D.L (j, true) = 0
  · simp only [negSteps, geomWalk, dif_pos h, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_nil, List.reverse_nil, List.filterMap_cons, DStep.edge?_skip,
      List.filterMap_nil]
  · simp only [negSteps, geomWalk, dif_neg h, SimpleGraph.Walk.edges_copy, List.filterMap_map,
      DStep.edge?_bwd, Function.comp_apply]
    rw [cellWalk_edges (a * (CayV.genE P (j, true))⁻¹) j (D.L (j, true)) le_rfl]
    rw [← List.map_reverse, ← List.filterMap_eq_map]
    rfl

/-! ## The main statement -/

theorem tWalkAux_edges {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (w : List (Fin P.n × Bool)) :
    (Work.ORDunwoody.Dunwoody.tWalkAux D a w).edges =
      (Work.ORDunwoody.Dunwoody.faceSteps D a w).filterMap Work.ORDunwoody.Dunwoody.DStep.edge? := by
  induction w generalizing a with
  | nil => simp only [tWalkAux_nil, SimpleGraph.Walk.edges_nil, faceSteps_nil,
      List.filterMap_nil]
  | cons x t ih =>
    obtain ⟨j, b⟩ := x
    cases b with
    | true =>
        simp only [tWalkAux_true, faceSteps_true, SimpleGraph.Walk.edges_append,
          List.filterMap_append, ih, geomWalk_edges]
    | false =>
        simp only [tWalkAux, faceSteps_false, SimpleGraph.Walk.edges_copy,
          SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse, List.filterMap_append,
          ih, negSteps_edges]

end Work.ORDunwoody
