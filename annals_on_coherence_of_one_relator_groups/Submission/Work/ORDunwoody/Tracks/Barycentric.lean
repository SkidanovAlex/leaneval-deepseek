/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The barycentric subdivision of a `G`-tree, as a `G`-tree

`Tracks/Level.lean` defines the barycentric subdivision `baryGraph T` of a `G`-tree `T` as an
explicit graph on the vertex type `BaryV G V T = V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet}`, proves
it is a tree (`baryGraph_isTree`), and proves the colour lemma
(`colour_const_of_avoids`).  `Lemmas/baryMulAction.lean` defines the induced `G`-action
(`barySmul`, `baryMulActionInst`) but only as an *existential*, since the vertex type is a
`Sum` type and the action therefore cannot be registered as a global instance without
touching `Sum` instances.

This file does the packaging: it registers the action as an instance and proves that it
preserves the subdivision graph, giving `baryGT T : GTree G (BaryV G V T)`.  This is what
the Dunwoody construction needs: the *target* of the cellular map `X̃ → T` is the subdivided
tree `T'`, so that the map can be taken cellular (every edge of the source maps to a single
edge of `T'` or to a point), after which the pattern and the colour lemma become
combinatorial (`RESOLUTION_PLAN.md`, Step A).
-/
import Submission.Work.ORDunwoody.Tracks.Level
import Submission.Work.ORDunwoody.Lemmas.baryMulAction

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open GTree

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]

/-- The `G`-action on the barycentric subdivision of a `G`-tree `T`, from
`Lemmas.baryMulAction`, registered as an instance so that `baryGraph T` can be used with the
typeclass-based `GTree` API. -/
noncomputable instance baryMulActionInstance (T : GTree G V) : MulAction G (BaryV G V T) :=
  Lemmas.baryMulActionInst T

/-- The induced action on the barycentric subdivision preserves adjacency. -/
theorem baryGraph_smul_adj (T : GTree G V) (g : G) {u v : BaryV G V T}
    (h : (baryGraph T).Adj u v) : (baryGraph T).Adj (g • u) (g • v) := by
  rcases u with a | e <;> rcases v with b | f
  · exact h
  · show (g • a : V) ∈ Sym2.map (fun w : V => g • w) (f : Sym2 V)
    exact Sym2.mem_map.mpr ⟨a, h, rfl⟩
  · show (g • b : V) ∈ Sym2.map (fun w : V => g • w) (e : Sym2 V)
    exact Sym2.mem_map.mpr ⟨b, h, rfl⟩
  · exact h

/-- **The barycentric subdivision of a `G`-tree, as a `G`-tree.**  The vertex type is
`BaryV G V T = V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet}` — vertices of `T` together with
("midpoints of") edges of `T`, the latter being adjacent exactly to the endpoints of the
edge. -/
noncomputable def baryGT (T : GTree G V) : GTree G (BaryV G V T) where
  graph := baryGraph T
  isTree := baryGraph_isTree T
  smul_adj := fun g _ _ h => baryGraph_smul_adj T g h

@[simp] theorem baryGT_graph (T : GTree G V) : (baryGT T).graph = baryGraph T := rfl

@[simp] theorem baryGT_adj_iff (T : GTree G V) (u v : BaryV G V T) :
    (baryGT T).Adj u v ↔ (baryGraph T).Adj u v := Iff.rfl

/-- The stabilizer of an original vertex of `T` inside the subdivided tree is the stabilizer
of that vertex in `T`. -/
@[simp] theorem baryGT_vertexStab_inl (T : GTree G V) (v : V) :
    (baryGT T).vertexStab (Sum.inl v) = T.vertexStab v := by
  ext g
  simp only [GTree.vertexStab, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact Sum.inl.inj h
  · intro h
    change Sum.inl (g • v) = Sum.inl v
    rw [h]

/-- An element fixes the midpoint of an edge of `T` in the subdivision exactly when it
preserves that edge. -/
theorem mem_baryGT_vertexStab_inr (T : GTree G V)
    (e : {e : Sym2 V // e ∈ T.graph.edgeSet}) (g : G) :
    g ∈ (baryGT T).vertexStab (Sum.inr e) ↔
      Sym2.map (fun v : V => g • v) (e : Sym2 V) = (e : Sym2 V) := by
  rw [GTree.vertexStab, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact congrArg Subtype.val (Sum.inr.inj h)
  · intro h
    exact congrArg Sum.inr (Subtype.ext h)

end Work.ORDunwoody
