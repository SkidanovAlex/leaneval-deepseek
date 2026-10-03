/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The partial subdivision as a `GTree`: definition and vertex stabilizers

`Tracks/PartialSubdivision.lean` defines the vertex type `PSubV R`, the action, and the graph
`psubGraph R` of the partial subdivision of a `G`-tree along a `G`-invariant set `R.edges` of
its edges.  This file packages `psubGraph R` as a `GTree G (PSubV R)` (given the proof that it
is a tree) and computes its vertex stabilizers:

* the stabilizer of an old vertex `Sum.inl v` is `R.tree.vertexStab v`;
* the stabilizer of a midpoint `Sum.inr e` is the *setwise* stabilizer of the edge `e`, i.e.
  `{g : G | Sym2.map (fun v => g • v) e = e}`.

It is kept separate from `partialSubdivision.lean` so that the cocompactness and
finite-generation lemmas can be stated and proved against `psubGT` without importing the proof
of `PartialSubdivision`.
-/
import Submission.Work.ORDunwoody.Tracks.PartialSubdivision

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open GTree

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]

/-- The partial subdivision of a `G`-tree along a `G`-invariant set of edges, as a `GTree`,
given the proof that its underlying graph is a tree. -/
noncomputable def psubGT (R : EdgeInv G V) (h : (psubGraph R).IsTree) : GTree G (PSubV R) where
  graph := psubGraph R
  isTree := h
  smul_adj := fun g _ _ hadj => psubGraph_smul_adj R g hadj

@[simp] theorem psubGT_graph (R : EdgeInv G V) (h : (psubGraph R).IsTree) :
    (psubGT R h).graph = psubGraph R := rfl

@[simp] theorem psubGT_adj_iff (R : EdgeInv G V) (h : (psubGraph R).IsTree) (a b : PSubV R) :
    (psubGT R h).Adj a b ↔ (psubGraph R).Adj a b := Iff.rfl

/-- The stabilizer of an old vertex of the partial subdivision is the stabilizer of that vertex
in the tree. -/
@[simp] theorem psubGT_vertexStab_inl (R : EdgeInv G V) (h : (psubGraph R).IsTree) (v : V) :
    (psubGT R h).vertexStab (Sum.inl v) = R.tree.vertexStab v := by
  ext g
  exact psubGraph_mem_vertexStab_inl R g v

/-- Membership in the stabilizer of an old vertex of the partial subdivision. -/
theorem psubGT_vertexStab_mem_inl (R : EdgeInv G V) (h : (psubGraph R).IsTree) (g : G) (v : V) :
    g ∈ (psubGT R h).vertexStab (Sum.inl v) ↔ g • v = v := by
  rw [GTree.vertexStab, MulAction.mem_stabilizer_iff, psub_smul_inl, Sum.inl.injEq]

/-- An element fixes a midpoint of the partial subdivision exactly when it preserves the
corresponding edge. -/
theorem psub_smul_inr_eq_iff (R : EdgeInv G V) (g : G) (e : {e : Sym2 V // e ∈ R.edges}) :
    g • (Sum.inr e : PSubV R) = Sum.inr e ↔
      Sym2.map (fun v : V => g • v) (e : Sym2 V) = (e : Sym2 V) := by
  rw [psub_smul_inr]
  constructor
  · intro hh
    exact congrArg Subtype.val (Sum.inr.inj hh)
  · intro hh
    exact congrArg Sum.inr (Subtype.ext hh)

/-- Membership in the stabilizer of an edge of a `G`-tree: an element stabilizes the edge
exactly when it fixes both endpoints. -/
theorem gTree_edgeStab_mem (T : GTree G V) {u w : V} (g : G) :
    g ∈ T.edgeStab u w ↔ (g • u = u ∧ g • w = w) := by
  rw [GTree.edgeStab_eq, Subgroup.mem_inf, GTree.vertexStab, GTree.vertexStab,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]

/-- An element of `G` fixes the midpoint of a marked edge of the partial subdivision exactly
when it preserves that edge setwise. -/
theorem psubGT_vertexStab_inr_mem (R : EdgeInv G V) (h : (psubGraph R).IsTree)
    (e : {e : Sym2 V // e ∈ R.edges}) (g : G) :
    g ∈ (psubGT R h).vertexStab (Sum.inr e) ↔
      Sym2.map (fun v : V => g • v) (e : Sym2 V) = (e : Sym2 V) := by
  rw [GTree.vertexStab, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    exact congrArg Subtype.val (Sum.inr.inj hg)
  · intro hg
    exact congrArg Sum.inr (Subtype.ext hg)

/-- The stabilizer of a midpoint of the partial subdivision is the setwise stabilizer of the
corresponding edge of the tree. -/
theorem psubGT_vertexStab_inr (R : EdgeInv G V) (h : (psubGraph R).IsTree)
    (e : {e : Sym2 V // e ∈ R.edges}) :
    ((psubGT R h).vertexStab (Sum.inr e) : Set G) =
      {g : G | Sym2.map (fun v : V => g • v) (e : Sym2 V) = (e : Sym2 V)} := by
  ext g
  exact psubGT_vertexStab_inr_mem R h e g

end Work.ORDunwoody
