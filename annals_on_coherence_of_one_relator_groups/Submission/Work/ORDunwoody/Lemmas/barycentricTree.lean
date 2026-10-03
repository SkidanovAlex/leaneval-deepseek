import Mathlib
import Submission.Work.ORDunwoody.Lemmas.barycentricDefs

namespace Work.ORDunwoody.Lemmas

/-- **The barycentric subdivision of a tree is a tree.**  For a tree `G` on `V`, subdivide every
edge: the vertex type becomes `V ⊕ {e // e ∈ G.edgeSet}` (original vertices plus edges of `G`),
each original vertex is joined exactly to the edges containing it, and no two vertices of the
same kind are joined.

This is the first ingredient of the "cellular" model of Dunwoody's resolution: subdividing the
target tree makes "the midpoint of an edge" a genuine vertex, so that a morphism of graphs from
the presentation 2-complex to the subdivided tree can be taken cellular (edges to edges or
points), and the pattern is then a set of *vertices* (the preimages of the subdivision
vertices). -/
theorem barycentricTree {V : Type*} (G : SimpleGraph V) (hG : G.IsTree) :
    ∃ G' : SimpleGraph (V ⊕ {e : Sym2 V // e ∈ G.edgeSet}),
      (∀ (v w : V), G'.Adj (Sum.inl v) (Sum.inl w) ↔ False) ∧
      (∀ (v : V) (e : {e : Sym2 V // e ∈ G.edgeSet}),
          G'.Adj (Sum.inl v) (Sum.inr e) ↔ v ∈ (e : Sym2 V)) ∧
      (∀ (e e' : {e : Sym2 V // e ∈ G.edgeSet}), G'.Adj (Sum.inr e) (Sum.inr e') ↔ False) ∧
      G'.IsTree := by
  refine ⟨barycentricGraph G, ?_, ?_, ?_, ?_⟩
  · intro v w
    exact barycentricGraph_adj_inl_inl v w
  · intro v e
    exact barycentricGraph_adj_inl_inr v e
  · intro e e'
    exact barycentricGraph_adj_inr_inr e e'
  · exact barycentricGraph_isTree hG

end Work.ORDunwoody.Lemmas
