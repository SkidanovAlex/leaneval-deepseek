import Mathlib

/-!
# Finite graphs presented by symmetric dart sets

A *dart* is a directed edge `(a, b)`.  A `DartGraph` is a finite set `D` of darts that is
symmetric (`e ∈ D → e.swap ∈ D`) and loopless (`e.1 ≠ e.2`).  The undirected edges of the graph
are the two-element orbits of `D` under `Prod.swap`.

The main use below is the statement that a graph all of whose degrees are even can be decomposed
into edge-disjoint cycles (`DartGraph.exists_cycle_decomposition`).
-/

namespace Work.HornSC.CellBoundaryJordan

/-- A finite graph, presented as a finite set `D` of *darts* (directed edges), closed under
reversal and without loops. -/
structure DartGraph (α : Type*) where
  D : Finset (α × α)
  symm : ∀ e ∈ D, e.swap ∈ D
  noLoop : ∀ e ∈ D, e.1 ≠ e.2

namespace DartGraph

variable {α : Type*} [DecidableEq α]

/-- The degree of `a`, counted as the number of darts of `G` leaving `a`.  For a symmetric dart
set this is the number of undirected edges of `G` through `a`. -/
def deg (G : DartGraph α) (a : α) : ℕ := (G.D.filter (fun e => e.1 = a)).card

/-- `a` and `b` are joined by an edge of `G`. -/
def Adj (G : DartGraph α) (a b : α) : Prop := (a, b) ∈ G.D

/-- A cycle of `G` of combinatorial length `L ≥ 3`: an `L`-periodic sequence whose first `L`
terms are pairwise distinct and whose consecutive pairs are darts of `G`. -/
structure Cycle (G : DartGraph α) where
  L : ℕ
  hL : 3 ≤ L
  w : ℕ → α
  per : ∀ j, w (j + L) = w j
  inj : ∀ i j, i < L → j < L → w i = w j → i = j
  adj : ∀ j, j < L → G.Adj (w j) (w (j + 1))

/-- The darts carried by a cycle, in both orientations. -/
def Cycle.darts {G : DartGraph α} (C : G.Cycle) : Finset (α × α) :=
  ((Finset.range C.L).image (fun j => (C.w j, C.w (j + 1)))) ∪
  ((Finset.range C.L).image (fun j => (C.w (j + 1), C.w j)))

lemma Cycle.mem_darts_forward {G : DartGraph α} (C : G.Cycle) {j : ℕ} (hj : j < C.L) :
    (C.w j, C.w (j + 1)) ∈ C.darts :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)

lemma Cycle.mem_darts_backward {G : DartGraph α} (C : G.Cycle) {j : ℕ} (hj : j < C.L) :
    (C.w (j + 1), C.w j) ∈ C.darts :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)

/-- A cycle is closed. -/
lemma Cycle.w_period {G : DartGraph α} (C : G.Cycle) : C.w C.L = C.w 0 := by
  have := C.per 0; simpa using this

/-- The dart set of a cycle is contained in `G.D`. -/
lemma Cycle.darts_subset {G : DartGraph α} (C : G.Cycle) : C.darts ⊆ G.D := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact C.adj j (Finset.mem_range.mp hj)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact G.symm _ (C.adj j (Finset.mem_range.mp hj))

/-- A cycle is symmetric as a dart set. -/
lemma Cycle.swap_mem_darts {G : DartGraph α} (C : G.Cycle) {e : α × α} (he : e ∈ C.darts) :
    e.swap ∈ C.darts := by
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact C.mem_darts_backward (Finset.mem_range.mp hj)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact C.mem_darts_forward (Finset.mem_range.mp hj)

end DartGraph
end Work.HornSC.CellBoundaryJordan
