/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Simplicial trees with a group action

This file sets up the combinatorial foundation used by `Submission.Work.ORDunwoody.*`:
simplicial trees (`SimpleGraph` + connected + acyclic) carrying a left action of a group
`G` by graph automorphisms, together with

* vertex and edge stabilizers, and finite generation of those stabilizers;
* cocompactness (finitely many orbits of vertices and of edges);
* equivariant morphisms ("domination maps") and collapse maps / refinements;
* the change-of-group operations (`restrict`, `pullback`) used to compare the tree
  actions of a group, of a subgroup, and of a quotient.

Trees are `GTree G V` where `V` is the vertex type, so that stabilizers are subgroups of
`G` and are directly comparable with the vocabulary of `ChallengeDeps`
(`Group.Coherent`, ...).
-/
import ChallengeDeps
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness

set_option autoImplicit false

set_option linter.unusedVariables false

universe u v w x

variable {G : Type u} {H : Type v} {V : Type w} {W : Type x}

namespace Work.ORDunwoody

open SimpleGraph

/-- A simplicial tree on the vertex type `V`, together with an action of the group `G`
by graph automorphisms. -/
structure GTree (G : Type u) [Group G] (V : Type w) [MulAction G V] where
  /-- The underlying graph. -/
  graph : SimpleGraph V
  /-- The underlying graph is a tree. -/
  isTree : graph.IsTree
  /-- The action preserves adjacency. -/
  smul_adj : ∀ (g : G) ⦃u v : V⦄, graph.Adj u v → graph.Adj (g • u) (g • v)

namespace GTree

section Basic

variable [Group G] [MulAction G V]

/-- The adjacency relation of the tree, as a definition. -/
abbrev Adj (T : GTree G V) (u v : V) : Prop := T.graph.Adj u v

@[simp] theorem adj_self (T : GTree G V) (v : V) : ¬ T.Adj v v := T.graph.irrefl

theorem adj_smul_iff (T : GTree G V) (g : G) {u v : V} :
    T.Adj (g • u) (g • v) ↔ T.Adj u v := by
  refine ⟨fun h => ?_, fun h => T.smul_adj g h⟩
  have := T.smul_adj g⁻¹ h
  simpa using this

theorem smul_adj' (T : GTree G V) (g : G) {u v : V} (h : T.Adj (g • u) (g • v)) : T.Adj u v :=
  (T.adj_smul_iff g).mp h

/-- The stabilizer of a vertex of the tree. -/
def vertexStab (T : GTree G V) (v : V) : Subgroup G := MulAction.stabilizer G v

/-- The stabilizer of an edge, i.e. the pointwise stabilizer of its two endpoints. -/
def edgeStab (T : GTree G V) (u v : V) : Subgroup G := MulAction.stabilizer G (u, v)

theorem edgeStab_eq (T : GTree G V) (u v : V) :
    T.edgeStab u v = T.vertexStab u ⊓ T.vertexStab v := by
  ext g
  simp [edgeStab, vertexStab, MulAction.mem_stabilizer_iff, Prod.ext_iff]

theorem edgeStab_comm (T : GTree G V) (u v : V) : T.edgeStab u v = T.edgeStab v u := by
  rw [edgeStab_eq, edgeStab_eq, inf_comm]

theorem vertexStab_smul (T : GTree G V) (g : G) (v : V) :
    T.vertexStab (g • v) = (T.vertexStab v).map (MulEquiv.toMonoidHom (MulAut.conj g)) :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g v

theorem edgeStab_smul (T : GTree G V) (g : G) (u v : V) :
    T.edgeStab (g • u) (g • v) =
      (T.edgeStab u v).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  rw [edgeStab_eq, edgeStab_eq, vertexStab_smul, vertexStab_smul,
    Subgroup.map_inf _ _ (MulEquiv.toMonoidHom (MulAut.conj g)) (MulAut.conj g).injective]

/-- All vertex stabilizers of the tree action are finitely generated. -/
def HasFGVertexStab (T : GTree G V) : Prop := ∀ v : V, (T.vertexStab v).FG

/-- All edge stabilizers of the tree action are finitely generated. -/
def HasFGEdgeStab (T : GTree G V) : Prop := ∀ u v : V, T.Adj u v → (T.edgeStab u v).FG

/-- All vertex and edge stabilizers are finitely generated. -/
def HasFGStab (T : GTree G V) : Prop := T.HasFGVertexStab ∧ T.HasFGEdgeStab

/-- The type of (ordered) adjacent pairs of vertices, i.e. of oriented edges. -/
abbrev AdjPair (T : GTree G V) : Type w := {p : V × V // T.Adj p.1 p.2}

instance (T : GTree G V) : MulAction G (AdjPair T) where
  smul g p := ⟨g • p.1, T.smul_adj g p.2⟩
  one_smul p := Subtype.ext (one_smul G p.1)
  mul_smul g h p := Subtype.ext (mul_smul g h p.1)

/-- The action of `G` on the tree is *cocompact* if there are only finitely many orbits
of vertices and finitely many orbits of edges. -/
def IsCocompact (T : GTree G V) : Prop :=
  Finite (MulAction.orbitRel.Quotient G V) ∧ Finite (MulAction.orbitRel.Quotient G (AdjPair T))

/-- The one-vertex tree, on which `G` acts trivially. -/
def trivial (G : Type u) [Group G] : GTree G PUnit where
  graph := ⊥
  isTree :=
    ⟨SimpleGraph.connected_bot_iff.mpr ⟨inferInstance, ⟨PUnit.unit⟩⟩,
      SimpleGraph.IsAcyclic.of_subsingleton⟩
  smul_adj := fun _ _ _ h => h

end Basic

section ChangeOfGroup

variable [Group G] [Group H] [MulAction G V]

/-- The same tree, with the action restricted to a subgroup. -/
def restrict (T : GTree G V) (K : Subgroup G) : GTree K V where
  graph := T.graph
  isTree := T.isTree
  smul_adj := fun k u v h => T.smul_adj (k : G) h

@[simp] theorem restrict_graph (T : GTree G V) (K : Subgroup G) :
    (T.restrict K).graph = T.graph := rfl

/-- The same tree, regarded as a tree for a group `H` acting through a homomorphism
`π : H →* G`.  The hypothesis `h` records that the `H`-action on `V` in scope is the one
induced by `π` (obtained with `MulAction.compHom`). -/
def pullback (T : GTree G V) (π : H →* G) [MulAction H V]
    (h : ∀ (a : H) (v : V), a • v = π a • v) : GTree H V where
  graph := T.graph
  isTree := T.isTree
  smul_adj := fun a u v hadj => by
    rw [h a u, h a v]
    exact T.smul_adj (π a) hadj

@[simp] theorem pullback_graph (T : GTree G V) (π : H →* G) [MulAction H V]
    (h : ∀ (a : H) (v : V), a • v = π a • v) : (T.pullback π h).graph = T.graph := rfl

end ChangeOfGroup

end GTree

open GTree

section Domination

variable [Group G] [MulAction G V] [MulAction G W]

/-- A `G`-equivariant morphism of trees: vertices go to vertices and edges go to edges or
to points. -/
structure DominationMap (S : GTree G V) (T : GTree G W) where
  /-- The underlying map on vertices. -/
  toFun : V → W
  /-- It is `G`-equivariant. -/
  map_smul' : ∀ (g : G) (v : V), toFun (g • v) = g • toFun v
  /-- It maps adjacent vertices to adjacent vertices or to equal vertices. -/
  map_adj' : ∀ ⦃u v : V⦄, S.Adj u v → T.Adj (toFun u) (toFun v) ∨ toFun u = toFun v

instance instCoeFun {S : GTree G V} {T : GTree G W} :
    CoeFun (DominationMap S T) (fun _ => V → W) where
  coe f := f.toFun

namespace DominationMap

variable {S : GTree G V} {T : GTree G W}

theorem map_smul (f : DominationMap S T) (g : G) (v : V) : f (g • v) = g • f v :=
  f.map_smul' g v

theorem map_adj (f : DominationMap S T) {u v : V} (h : S.Adj u v) :
    T.Adj (f u) (f v) ∨ f u = f v := f.map_adj' h

/-- A domination map maps vertex stabilizers into vertex stabilizers. -/
theorem vertexStab_le (f : DominationMap S T) (v : V) : S.vertexStab v ≤ T.vertexStab (f v) := by
  intro g hg
  rw [vertexStab, MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← map_smul f g v, hg]

theorem edgeStab_le (f : DominationMap S T) {u v : V} (h : S.Adj u v) :
    S.edgeStab u v ≤ T.edgeStab (f u) (f v) := by
  rw [edgeStab_eq, edgeStab_eq]
  exact le_inf (le_trans inf_le_left (vertexStab_le f u))
    (le_trans inf_le_right (vertexStab_le f v))

/-- The identity domination map. -/
def id (S : GTree G V) : DominationMap S S where
  toFun := _root_.id
  map_smul' := fun _ _ => rfl
  map_adj' := by intro u v h; exact Or.inl h

/-- Composition of domination maps. -/
def comp {U : Type*} [MulAction G U] {S : GTree G V} {T : GTree G W} {R : GTree G U}
    (f : DominationMap S T) (g : DominationMap T R) : DominationMap S R where
  toFun := g ∘ f
  map_smul' := fun a v => by simp only [Function.comp_apply, map_smul]
  map_adj' := by
    intro u v h
    rcases f.map_adj h with h' | h'
    · exact g.map_adj h'
    · exact Or.inr (by simp only [Function.comp_apply, h'])

end DominationMap

/-- `S` dominates `T` if there is a `G`-equivariant morphism `S → T`. -/
def Dominates (S : GTree G V) (T : GTree G W) : Prop := Nonempty (DominationMap S T)

theorem dominates_refl (S : GTree G V) : Dominates S S := ⟨DominationMap.id S⟩

theorem Dominates.trans {S : GTree G V} {T : GTree G W} {U : Type*}
    [MulAction G U] {R : GTree G U} (h₁ : Dominates S T) (h₂ : Dominates T R) :
    Dominates S R :=
  ⟨DominationMap.comp h₁.some h₂.some⟩

/-- A collapse map: a domination map whose fibres are connected.  This is the map obtained
by collapsing a `G`-invariant family of edges to vertices. -/
structure CollapseMap (S : GTree G V) (T : GTree G W) extends DominationMap S T where
  /-- The map is onto. -/
  surj : Function.Surjective toFun
  /-- Fibres are connected. -/
  fiber_reachable : ∀ ⦃u v : V⦄, toFun u = toFun v → S.graph.Reachable u v

/-- `S` refines `T`: `T` is obtained from `S` by collapsing edges. -/
def Refinement (S : GTree G V) (T : GTree G W) : Prop := Nonempty (CollapseMap S T)

theorem refinement_refl (S : GTree G V) : Refinement S S :=
  ⟨{ toFun := _root_.id
     map_smul' := fun _ _ => rfl
     map_adj' := by intro u v h; exact Or.inl h
     surj := fun v => ⟨v, rfl⟩
     fiber_reachable := by
       intro u v h
       subst h
       exact ⟨SimpleGraph.Walk.nil⟩ }⟩

theorem Refinement.dominates {S : GTree G V} {T : GTree G W} (h : Refinement S T) :
    Dominates S T :=
  ⟨h.some.toDominationMap⟩

end Domination

section OverHom

variable [Group G] [Group H] [MulAction H V] [MulAction G W]

/-- A `π`-equivariant morphism from an `H`-tree to a `G`-tree, where `π : H →* G`. -/
structure DominationMapOver (π : H →* G) (S : GTree H V) (T : GTree G W) where
  /-- The underlying map on vertices. -/
  toFun : V → W
  /-- It is equivariant with respect to `π`. -/
  map_smul' : ∀ (h : H) (v : V), toFun (h • v) = π h • toFun v
  /-- It maps adjacent vertices to adjacent vertices or to equal vertices. -/
  map_adj' : ∀ ⦃u v : V⦄, S.Adj u v → T.Adj (toFun u) (toFun v) ∨ toFun u = toFun v

instance instCoeFunOver {π : H →* G} {S : GTree H V} {T : GTree G W} :
    CoeFun (DominationMapOver π S T) (fun _ => V → W) where
  coe f := f.toFun

namespace DominationMapOver

variable {π : H →* G} {S : GTree H V} {T : GTree G W}

theorem map_smul (f : DominationMapOver π S T) (h : H) (v : V) : f (h • v) = π h • f v :=
  f.map_smul' h v

theorem map_adj (f : DominationMapOver π S T) {u v : V} (h : S.Adj u v) :
    T.Adj (f u) (f v) ∨ f u = f v := f.map_adj' h

/-- The image of a vertex stabilizer under `π` is contained in the stabilizer of the image
vertex. -/
theorem vertexStab_map_le (f : DominationMapOver π S T) (v : V) :
    (S.vertexStab v).map π ≤ T.vertexStab (f v) := by
  rintro _ ⟨h, hh, rfl⟩
  have hv : h • v = v := hh
  show π h • f v = f v
  rw [← f.map_smul h v, hv]

/-- Composition of morphisms over homomorphisms. -/
def comp {K : Type x} {U : Type x} [Group K] [MulAction K U] {σ : K →* H} {S' : GTree K U}
    (f : DominationMapOver σ S' S) (g : DominationMapOver π S T) :
    DominationMapOver (π.comp σ) S' T where
  toFun := g ∘ f
  map_smul' := fun k u => by simp only [Function.comp_apply, map_smul, MonoidHom.comp_apply]
  map_adj' := by
    intro u v h
    rcases f.map_adj h with h' | h'
    · exact g.map_adj h'
    · exact Or.inr (by simp only [Function.comp_apply, h'])

end DominationMapOver

/-- The identity as a morphism over `MonoidHom.id G`. -/
def DominationMapOver.id [MulAction G V] (T : GTree G V) :
    DominationMapOver (MonoidHom.id G) T T where
  toFun := _root_.id
  map_smul' := fun h v => rfl
  map_adj' := by intro u v h; exact Or.inl h

/-- `S` dominates `T` over `π : H →* G`. -/
def DominatesOver (π : H →* G) (S : GTree H V) (T : GTree G W) : Prop :=
  Nonempty (DominationMapOver π S T)

theorem DominatesOver.trans {K : Type x} {U : Type x} [Group K] [MulAction K U]
    {σ : K →* H} {π : H →* G}
    {S' : GTree K U} {S : GTree H V} {T : GTree G W} (h₁ : DominatesOver σ S' S)
    (h₂ : DominatesOver π S T) : DominatesOver (π.comp σ) S' T :=
  ⟨DominationMapOver.comp h₁.some h₂.some⟩


/-- Composition of a domination map over `π : H →* G` with an ordinary domination map of
`H`-trees. -/
def DominationMapOver.compDominationMap {U : Type x} [MulAction H U] {S₂ : GTree H U}
    {S : GTree H V} {T : GTree G W} {π : H →* G} (f : DominationMap S₂ S)
    (g : DominationMapOver π S T) : DominationMapOver π S₂ T where
  toFun := g ∘ f
  map_smul' := fun h u => by simp only [Function.comp_apply, f.map_smul', g.map_smul']
  map_adj' := by
    intro u v huv
    rcases f.map_adj huv with h' | h'
    · exact g.map_adj h'
    · exact Or.inr (by simp only [Function.comp_apply, h'])

theorem DominatesOver.trans_dominates {U : Type x} [MulAction H U] {S₂ : GTree H U}
    {S : GTree H V} {T : GTree G W} {π : H →* G} (h₁ : Dominates S₂ S)
    (h₂ : DominatesOver π S T) : DominatesOver π S₂ T :=
  ⟨DominationMapOver.compDominationMap h₁.some h₂.some⟩

theorem dominatesOver_iff_dominates [MulAction G V] (S : GTree G V) (T : GTree G W) :
    DominatesOver (MonoidHom.id G) S T ↔ Dominates S T := by
  constructor
  · rintro ⟨f⟩
    exact ⟨{ toFun := f.toFun
             map_smul' := fun g v => by simpa using f.map_smul' g v
             map_adj' := f.map_adj' }⟩
  · rintro ⟨f⟩
    exact ⟨{ toFun := f.toFun
             map_smul' := fun g v => by simpa using f.map_smul' g v
             map_adj' := f.map_adj' }⟩

theorem dominatesOver_iff_dominates_pullback [MulAction H W]
    (π : H →* G) (hcompat : ∀ (a : H) (w : W), a • w = π a • w) (S : GTree H V)
    (T : GTree G W) :
    DominatesOver π S T ↔ Dominates S (T.pullback π hcompat) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨{ toFun := f.toFun
             map_smul' := fun h v => by rw [f.map_smul' h v, hcompat]
             map_adj' := f.map_adj' }⟩
  · rintro ⟨f⟩
    exact ⟨{ toFun := f.toFun
             map_smul' := fun h v => by rw [f.map_smul' h v, hcompat]
             map_adj' := f.map_adj' }⟩

end OverHom

end Work.ORDunwoody
