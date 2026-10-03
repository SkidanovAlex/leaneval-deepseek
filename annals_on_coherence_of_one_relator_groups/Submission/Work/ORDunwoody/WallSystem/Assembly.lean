/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Assembling the resolution tree from a wall system

`WallSystem/Basic.lean` proves that the dual graph of a wall system is acyclic, hence a tree when
connected.  This file packages that dual graph as a `GTree` and produces the domination map
`S → T` from the *colour* map of the pattern (`Tracks/Level.lean`, `colour_const_of_avoids`).

The remaining inputs of `dunwoodyResolution` are then exactly the geometric ones
(`DESIGN_N13.md`, §4): cocompactness of the wall system, finite generation of the stabilisers of
its walls and regions, and the construction of the wall system (and its colours) from the
pattern.
-/
import Submission.Work.ORDunwoody.WallSystem.Basic
import Submission.Work.ORDunwoody.Basic

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.WallSystem

variable {G : Type u} [Group G] {Wall Region V : Type u} [MulAction G Region] [MulAction G Wall]
  [MulAction G V]

/-- The dual graph of a wall system is invariant under a `G`-action that preserves the
incidence relation. -/
theorem wallSystem_graph_smul_adj (S : System Wall Region)
    (hinc : ∀ (g : G) ⦃w : Wall⦄ ⦃a b : Region⦄, S.Inc w a b →
      S.Inc (g • w) (g • a) (g • b))
    (g : G) {a b : Region} (h : S.graph.Adj a b) : S.graph.Adj (g • a) (g • b) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨g • w, hinc g hw⟩

/-- **The resolution tree of a wall system**: the dual graph, with the induced `G`-action, is a
tree as soon as it is connected. -/
def dualGT (S : System Wall Region)
    (hinc : ∀ (g : G) ⦃w : Wall⦄ ⦃a b : Region⦄, S.Inc w a b →
      S.Inc (g • w) (g • a) (g • b))
    (hconn : S.graph.Connected) : GTree G Region where
  graph := S.graph
  isTree := S.isTree hconn
  smul_adj := fun g _ _ h => wallSystem_graph_smul_adj S hinc g h

@[simp] theorem dualGT_graph (S : System Wall Region)
    (hinc : ∀ (g : G) ⦃w : Wall⦄ ⦃a b : Region⦄, S.Inc w a b →
      S.Inc (g • w) (g • a) (g • b))
    (hconn : S.graph.Connected) : (dualGT S hinc hconn).graph = S.graph := rfl

/-- **The domination map**: a region is sent to its colour in the tree `T`
(`Tracks/Level.lean`), which is `G`-equivariant and maps edges to edges or to points. -/
def dualDominationMap {T : GTree G V} (S : System Wall Region)
    (hinc : ∀ (g : G) ⦃w : Wall⦄ ⦃a b : Region⦄, S.Inc w a b →
      S.Inc (g • w) (g • a) (g • b))
    (hconn : S.graph.Connected) (c : Region → V)
    (hc_smul : ∀ (g : G) (a : Region), c (g • a) = g • c a)
    (hc_adj : ∀ ⦃a b : Region⦄, S.graph.Adj a b → T.Adj (c a) (c b) ∨ c a = c b) :
    DominationMap (dualGT S hinc hconn) T where
  toFun := c
  map_smul' := hc_smul
  map_adj' := hc_adj

theorem dualGT_dominates {T : GTree G V} (S : System Wall Region)
    (hinc : ∀ (g : G) ⦃w : Wall⦄ ⦃a b : Region⦄, S.Inc w a b →
      S.Inc (g • w) (g • a) (g • b))
    (hconn : S.graph.Connected) (c : Region → V)
    (hc_smul : ∀ (g : G) (a : Region), c (g • a) = g • c a)
    (hc_adj : ∀ ⦃a b : Region⦄, S.graph.Adj a b → T.Adj (c a) (c b) ∨ c a = c b) :
    Dominates (dualGT S hinc hconn) T :=
  ⟨dualDominationMap S hinc hconn c hc_smul hc_adj⟩

end Work.ORDunwoody
