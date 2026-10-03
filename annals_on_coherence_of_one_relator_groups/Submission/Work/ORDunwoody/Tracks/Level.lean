/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The level structure of a cellular map to a tree

This is the first layer of the construction of Dunwoody's resolution (`RESOLUTION_PLAN.md`).

Given a `G`-tree `T`, form its **barycentric subdivision** `baryGraph T`: the tree whose
vertices are the vertices *and* the (undirected) edges of `T`, an original vertex being joined
exactly to the edges containing it (this is a tree, `baryGraph_isTree`, from
`Lemmas.barycentricTree`).  Its edge-vertices are the "midpoints" of the edges of `T`, so a map
from a graph into `baryGraph T` can be taken *cellular* — an edge of the source maps to an edge
or to a point — and the preimage `P` of the edge-vertices is a set of *vertices* of the source.

The key structural fact, and the reason for subdividing, is `colour_const_of_avoids`:

> a cellular map from a graph `Γ` into `baryGraph T` is constant on the vertex set of any
> connected subgraph of `Γ` that avoids `P`.

Applied to the presentation 2-complex this is the *colour lemma*: every region of the pattern
(the connected pieces of `X̃ ∖ P`) maps into a single vertex-star, i.e. gets a colour in
`V(T)`; the resulting map on regions is the domination map `S → T` of the resolution.
-/
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORDunwoody.Lemmas.barycentricTree

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

open GTree

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]

/-- The vertex type of the barycentric subdivision of a `G`-tree: the vertices of `T` together
with the (undirected) edges of `T`. -/
abbrev BaryV (G : Type u) (V : Type u) [Group G] [MulAction G V] (T : GTree G V) : Type u :=
  V ⊕ {e : Sym2 V // e ∈ T.graph.edgeSet}

/-- The underlying `Sym2 V` of a subdivision vertex.  -/
def barySym2 (T : GTree G V) (a : BaryV G V T) : Option (Sym2 V) :=
  match a with
  | Sum.inl _ => none
  | Sum.inr e => some (e : Sym2 V)

/-- The barycentric subdivision of a `G`-tree, as an explicit graph: an original vertex is
adjacent exactly to the edges of `T` containing it, and no two vertices of the same kind are
adjacent. -/
def baryGraph (T : GTree G V) : SimpleGraph (BaryV G V T) where
  Adj a b := match a, b with
    | Sum.inl v, Sum.inr e => (v : V) ∈ (e : Sym2 V)
    | Sum.inr e, Sum.inl v => (v : V) ∈ (e : Sym2 V)
    | _, _ => False
  symm := ⟨by
    intro a b h
    rcases a with v | e <;> rcases b with w | f <;> exact h⟩
  loopless := ⟨by
    intro a h
    rcases a with v | e <;> exact h⟩

theorem baryGraph_adj_inl_inr (T : GTree G V)
    (v : V) (e : {e : Sym2 V // e ∈ T.graph.edgeSet}) :
    (baryGraph T).Adj (Sum.inl v) (Sum.inr e) ↔ (v : V) ∈ (e : Sym2 V) := Iff.rfl

theorem baryGraph_adj_inl_inl (T : GTree G V) (v w : V) :
    (baryGraph T).Adj (Sum.inl v) (Sum.inl w) ↔ False := Iff.rfl

theorem baryGraph_not_adj_inl_inl (T : GTree G V) (v w : V) :
    ¬ (baryGraph T).Adj (Sum.inl v) (Sum.inl w) := by
  rw [baryGraph_adj_inl_inl]; exact id

theorem baryGraph_adj_inr_inr (T : GTree G V)
    (e e' : {e : Sym2 V // e ∈ T.graph.edgeSet}) :
    (baryGraph T).Adj (Sum.inr e) (Sum.inr e') ↔ False := Iff.rfl

theorem baryGraph_not_adj_inr_inr (T : GTree G V)
    (e e' : {e : Sym2 V // e ∈ T.graph.edgeSet}) :
    ¬ (baryGraph T).Adj (Sum.inr e) (Sum.inr e') := by
  rw [baryGraph_adj_inr_inr]; exact id

theorem baryGraph_adj_inr_inl (T : GTree G V)
    (v : V) (e : {e : Sym2 V // e ∈ T.graph.edgeSet}) :
    (baryGraph T).Adj (Sum.inr e) (Sum.inl v) ↔ (v : V) ∈ (e : Sym2 V) := Iff.rfl

/-- The barycentric subdivision of a tree is a tree. -/
theorem baryGraph_isTree (T : GTree G V) : (baryGraph T).IsTree := by
  obtain ⟨G', h1, h2, h3, htree⟩ := Lemmas.barycentricTree T.graph T.isTree
  have hEq : G' = baryGraph T := by
    ext a b
    rcases a with v | e <;> rcases b with w | f
    · rw [h1, baryGraph_adj_inl_inl]
    · rw [h2, baryGraph_adj_inl_inr]
    · rw [baryGraph_adj_inr_inl, SimpleGraph.adj_comm, h2]
    · rw [h3, baryGraph_adj_inr_inr]
  rwa [hEq] at htree

/-- **The colour lemma.**  A cellular map from a graph `Γ` into the barycentric subdivision of a
tree is constant on the vertex set of any connected subgraph of `Γ` whose vertices do not map to
edge-vertices of the subdivision (i.e. avoid the "midpoints"). -/
theorem colour_const_of_avoids {V' : Type u} (Γ : SimpleGraph V') (T : GTree G V)
    (ψ : V' → BaryV G V T)
    (hψ : ∀ ⦃a b : V'⦄, Γ.Adj a b →
      ψ a = ψ b ∨ (baryGraph T).Adj (ψ a) (ψ b))
    (hmid : ∀ (a : V') (e : {e : Sym2 V // e ∈ T.graph.edgeSet}), ψ a ≠ Sum.inr e)
    {a b : V'} (w : Γ.Walk a b) : ψ a = ψ b := by
  induction w with
  | nil => rfl
  | cons hab _ ih =>
      rcases hψ hab with h' | h'
      · exact h'.trans ih
      · -- both images are `Sum.inl`-vertices, but those are never adjacent
        exfalso
        rcases ha : ψ _ with v | e
        · rcases hc : ψ _ with w | f
          · rw [ha, hc] at h'
            exact h'
          · exact hmid _ f hc
        · exact hmid _ e ha

end Work.ORDunwoody
