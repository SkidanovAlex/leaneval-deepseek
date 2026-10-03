/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The partial subdivision of a `G`-tree

`Tracks/Level.lean` and `Tracks/Barycentric.lean` subdivide *every* edge of a `G`-tree.  The
descent step of JL Theorem 4.4 needs the *partial* subdivision: subdivide only the edges of a
given `G`-invariant set `R`, keeping the other edges as they are.

Why the partial version is what is needed: in the descent step one must quotient a tree by the
normal closure `K` of the vertex stabilizers of the action of `N = ker π` on it.  Elements of
`N` that *invert* an edge `{u,v}` of `S'` have no fixed vertex, so they are not absorbed by
`K`; subdividing that edge turns them into elements fixing the new midpoint, and hence into
elements of `K`.  But subdividing *all* edges creates a midpoint for every edge, and a midpoint
of an edge `e` that is inverted by `h ∈ H` and not collapsed by the domination map `f₂ : S' → T`
would have to be mapped to a `π h`-fixed vertex of `T` — which does not exist.  Subdividing
only the edges that `f₂` collapses avoids this: those midpoints cause no constraint at all.

This file contains the definitions (the invariant edge set, the vertex type of the subdivision,
the induced action, and the graph).  `Tracks/partialSubdivision_isTree.lean` proves that the
graph is a tree, and `Hypotheses.PartialSubdivision` records the resulting service.
-/
import Submission.Work.ORDunwoody.Basic

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open GTree

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]

/-- A `G`-invariant set of (undirected) edges of a `G`-tree.  The tree is part of the data, so
that the vertex type of the partial subdivision and its `G`-action can be recovered from `R`
alone. -/
structure EdgeInv (G : Type u) [Group G] (V : Type u) [MulAction G V] where
  /-- The tree whose edges are marked. -/
  tree : GTree G V
  /-- The set of marked edges. -/
  edges : Set (Sym2 V)
  /-- Every marked element is a genuine edge of the tree. -/
  isEdge : ∀ e ∈ edges, e ∈ tree.graph.edgeSet
  /-- The set is invariant under the action of `G`. -/
  smul_mem : ∀ (g : G) ⦃e : Sym2 V⦄, e ∈ edges → Sym2.map (fun v : V => g • v) e ∈ edges

/-- The vertex type of the partial subdivision of `R.tree` along `R`: the old vertices of the
tree, together with the midpoints of the marked edges. -/
abbrev PSubV (R : EdgeInv G V) : Type u := V ⊕ {e : Sym2 V // e ∈ R.edges}

/-- The action of `G` on the partial subdivision: old vertices go to old vertices and midpoints
of marked edges go to midpoints of marked edges (the action on the old vertices being the given
one, and on the midpoints the induced action on edges). -/
noncomputable instance psubMulActionInst (R : EdgeInv G V) : MulAction G (PSubV R) where
  smul g z := match z with
    | Sum.inl v => Sum.inl (g • v)
    | Sum.inr e => Sum.inr ⟨Sym2.map (fun v : V => g • v) (e : Sym2 V), R.smul_mem g e.2⟩
  one_smul z := by
    rcases z with v | e
    · exact congrArg Sum.inl (one_smul G v)
    · refine congrArg Sum.inr (Subtype.ext ?_)
      change Sym2.map (fun v : V => (1 : G) • v) (e : Sym2 V) = (e : Sym2 V)
      induction (e : Sym2 V) using Sym2.ind with
      | h a b => simp [one_smul G a, one_smul G b]
  mul_smul g h z := by
    rcases z with v | e
    · exact congrArg Sum.inl (mul_smul g h v)
    · refine congrArg Sum.inr (Subtype.ext ?_)
      change Sym2.map (fun v : V => (g * h) • v) (e : Sym2 V) =
        Sym2.map (fun v : V => g • v) (Sym2.map (fun v : V => h • v) (e : Sym2 V))
      induction (e : Sym2 V) using Sym2.ind with
      | h a b => simp [mul_smul]

/-- The same action, stated for the unfolded vertex type. -/
noncomputable instance psubMulActionInst' (R : EdgeInv G V) :
    MulAction G (V ⊕ {e : Sym2 V // e ∈ R.edges}) := psubMulActionInst R

@[simp] theorem psub_smul_inl (R : EdgeInv G V) (g : G) (v : V) :
    g • (Sum.inl v : PSubV R) = Sum.inl (g • v) := rfl

@[simp] theorem psub_smul_inr (R : EdgeInv G V) (g : G)
    (e : {e : Sym2 V // e ∈ R.edges}) :
    g • (Sum.inr e : PSubV R) =
      Sum.inr ⟨Sym2.map (fun v : V => g • v) (e : Sym2 V), R.smul_mem g e.2⟩ := rfl

/-- The partial subdivision graph: the unmarked edges of `R.tree` are kept (as edges between
old vertices) and the marked edges are subdivided (each old vertex being joined to the midpoint
of each marked edge containing it). -/
def psubGraph (R : EdgeInv G V) : SimpleGraph (PSubV R) where
  Adj a b := match a, b with
    | Sum.inl u, Sum.inl v => R.tree.Adj u v ∧ s(u, v) ∉ R.edges
    | Sum.inl u, Sum.inr e => u ∈ (e : Sym2 V)
    | Sum.inr e, Sum.inl v => v ∈ (e : Sym2 V)
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro a b h
    rcases a with u | e <;> rcases b with v | f
    · exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro a h
    rcases a with u | e
    · exact R.tree.graph.irrefl h.1
    · exact h⟩

@[simp] theorem psubGraph_adj_inl_inl (R : EdgeInv G V) (u v : V) :
    (psubGraph R).Adj (Sum.inl u) (Sum.inl v) ↔ R.tree.Adj u v ∧ s(u, v) ∉ R.edges := Iff.rfl

@[simp] theorem psubGraph_adj_inl_inr (R : EdgeInv G V) (u : V)
    (e : {e : Sym2 V // e ∈ R.edges}) :
    (psubGraph R).Adj (Sum.inl u) (Sum.inr e) ↔ u ∈ (e : Sym2 V) := Iff.rfl

@[simp] theorem psubGraph_adj_inr_inl (R : EdgeInv G V) (v : V)
    (e : {e : Sym2 V // e ∈ R.edges}) :
    (psubGraph R).Adj (Sum.inr e) (Sum.inl v) ↔ v ∈ (e : Sym2 V) := Iff.rfl

@[simp] theorem psubGraph_adj_inr_inr (R : EdgeInv G V)
    (e e' : {e : Sym2 V // e ∈ R.edges}) :
    ¬ (psubGraph R).Adj (Sum.inr e) (Sum.inr e') := id

/-- The induced action preserves the adjacency relation of the partial subdivision. -/
theorem psubGraph_smul_adj (R : EdgeInv G V) (g : G) {a b : PSubV R}
    (h : (psubGraph R).Adj a b) : (psubGraph R).Adj (g • a) (g • b) := by
  rcases a with u | e <;> rcases b with v | f
  · -- two old vertices
    obtain ⟨h1, h2⟩ := h
    refine ⟨R.tree.smul_adj g h1, ?_⟩
    intro hmem
    apply h2
    have h1' : Sym2.map (fun v : V => g⁻¹ • v) (s(g • u, g • v)) ∈ R.edges :=
      R.smul_mem g⁻¹ hmem
    rwa [Sym2.map_mk, inv_smul_smul, inv_smul_smul] at h1'
  · -- old vertex and midpoint
    exact Sym2.mem_map.mpr ⟨u, h, rfl⟩
  · exact Sym2.mem_map.mpr ⟨v, h, rfl⟩
  · exact h

/-- The stabilizer of an old vertex of the partial subdivision is the stabilizer of that vertex
in the tree. -/
@[simp] theorem psubGraph_mem_vertexStab_inl (R : EdgeInv G V) (g : G) (v : V) :
    g ∈ MulAction.stabilizer G (Sum.inl v : PSubV R) ↔ g ∈ MulAction.stabilizer G v := by
  constructor
  · intro h
    exact Sum.inl.inj h
  · intro h
    show g • (Sum.inl v : PSubV R) = Sum.inl v
    rw [psub_smul_inl]
    exact congrArg (fun w : V => (Sum.inl w : PSubV R)) h

end Work.ORDunwoody
