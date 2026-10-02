import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# The degree in `graphOf 𝓖` is `degAt 𝓖 v`

For a 2-uniform hypergraph `𝓖` (all edges of size `2`) the neighbourhood of a
vertex `v` in the underlying simple graph `graphOf 𝓖` is exactly the 2-graph
neighbourhood `nbrs 𝓖 v`: both consist of the vertices `w` with `{v, w} ∈ 𝓖`,
and 2-uniformity rules out `w = v` (the edge `{v, v} = {v}` would have size
`1 ≠ 2`).  Hence `Nat.card ((graphOf 𝓖).neighborSet v) = degAt 𝓖 v`, the
cardinality of `nbrs 𝓖 v`.
-/

namespace Work.Deep.GKO

/-- Under 2-uniformity no vertex is its own 2-graph neighbour: `w = v` would
make the edge `{v, w} = {v}`, of size `1 ≠ 2`. -/
private theorem ne_of_mem_nbrs {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) (v : Fin n) :
    ∀ w : Fin n, w ∈ ErdosFaberLovaszConjecture.nbrs 𝓖 v → w ≠ v := by
  intro w hw hwv
  have hsz : ErdosFaberLovaszConjecture.edgeSize ({v, w} : Set (Fin n)) = 2 := h2 _ hw
  rw [hwv] at hsz
  have hp : ({v, v} : Set (Fin n)) = ({v} : Set (Fin n)) := by ext x; simp
  rw [hp, ErdosFaberLovaszConjecture.edgeSize_eq_ncard, Set.ncard_singleton] at hsz
  omega

/-- Under 2-uniformity the graph neighbourhood of `v` in `graphOf 𝓖` is the
2-graph neighbourhood `nbrs 𝓖 v`. -/
private theorem neighborSet_eq_nbrs {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) (v : Fin n) :
    (Work.Deep.GKO.graphOf 𝓖).neighborSet v = ErdosFaberLovaszConjecture.nbrs 𝓖 v := by
  ext w
  rw [SimpleGraph.mem_neighborSet, Work.Deep.GKO.graphOf_adj]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Ne.symm (ne_of_mem_nbrs 𝓖 h2 v w h), h⟩

/-- The degree of a vertex in `graphOf 𝓖` is `degAt 𝓖 v`, for a 2-uniform `𝓖`: under `h2` the neighbourhood of `v` in the graph (the vertices `w ≠ v` with `{v,w} ∈ 𝓖`) is exactly `nbrs 𝓖 v`, whose `ncard` is `degAt`.  Without `h2` the singleton edge `{v}` would inflate `degAt`. -/
theorem degree_graphOf {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) (v : Fin n) :
    Nat.card ((Work.Deep.GKO.graphOf 𝓖).neighborSet v) = ErdosFaberLovaszConjecture.degAt 𝓖 v := by
  rw [neighborSet_eq_nbrs 𝓖 h2 v, Nat.card_coe_set_eq]
  rfl

end Work.Deep.GKO
