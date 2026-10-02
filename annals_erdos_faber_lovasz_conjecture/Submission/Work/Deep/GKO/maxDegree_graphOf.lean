import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# The maximum degree of `graphOf 𝓖` is `hypergraphMaxDegree 𝓖`

For a 2-uniform hypergraph `𝓖` (every edge of size `2`), the maximum degree of the
underlying simple graph `graphOf 𝓖` coincides with the maximum vertex degree
`Δ(𝓖) = max_v d_𝓖(v)` of the hypergraph.

Both sides are suprema over the same vertex set `Fin n`; the entrywise fact is that
`Nat.card ((graphOf 𝓖).neighborSet v) = hypergraphDegree 𝓖 v`, proved here as
`natCard_neighborSet_graphOf`: the neighbourhood of `v` in the graph is the set of
`w ≠ v` with `{v, w} ∈ 𝓖`, which under `h2` is exactly `nbrs 𝓖 v` (no `w = v` can
satisfy `{v, v} = {v} ∈ 𝓖`, since that edge has size `1`), and the `ncard` of
`nbrs 𝓖 v` is `hypergraphDegree 𝓖 v` by `ncard_nbrs_eq_hypergraphDegree`.

The per-vertex fact is re-proved here rather than imported from
`Work.Deep.GKO.degree_graphOf` so that this module does not rest on any
unproved input.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open ErdosFaberLovaszConjecture (nbrs degAt edgeSize hypergraphDegree hypergraphMaxDegree
  edgeSize_eq_ncard ncard_nbrs_eq_hypergraphDegree)

namespace Work.Deep.GKO

/-- The degree of `v` in `graphOf 𝓖` is `hypergraphDegree 𝓖 v`, for a 2-uniform `𝓖`:
the neighbourhood of `v` in the graph (the vertices `w ≠ v` with `{v,w} ∈ 𝓖`) is
exactly `nbrs 𝓖 v`, whose `ncard` is `hypergraphDegree` by
`ncard_nbrs_eq_hypergraphDegree`. -/
theorem natCard_neighborSet_graphOf {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) (v : Fin n) :
    Nat.card ((Work.Deep.GKO.graphOf 𝓖).neighborSet v) = hypergraphDegree 𝓖 v := by
  have hset : (Work.Deep.GKO.graphOf 𝓖).neighborSet v = nbrs 𝓖 v := by
    ext w
    show (v ≠ w ∧ ({v, w} : Set (Fin n)) ∈ 𝓖) ↔ ({v, w} : Set (Fin n)) ∈ 𝓖
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      intro hne
      rw [hne] at h
      have hp : ({w, w} : Set (Fin n)) = ({w} : Set (Fin n)) := by ext x; simp
      rw [hp] at h
      have hsz := h2 _ h
      rw [edgeSize_eq_ncard, Set.ncard_singleton] at hsz
      omega
  rw [hset, Nat.card_coe_set_eq]
  exact ncard_nbrs_eq_hypergraphDegree h2 v

/-- The maximum degree of `graphOf 𝓖` is `hypergraphMaxDegree 𝓖`, for a 2-uniform `𝓖`.  Both sides are suprema over the same vertex set of the same function, by `degree_graphOf` and `ncard_nbrs_eq_hypergraphDegree`. -/
theorem maxDegree_graphOf {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) :
    Work.Deep.GKO.maxDeg (Work.Deep.GKO.graphOf 𝓖) = ErdosFaberLovaszConjecture.hypergraphMaxDegree 𝓖 := by
  unfold Work.Deep.GKO.maxDeg ErdosFaberLovaszConjecture.hypergraphMaxDegree
  exact Finset.sup_congr rfl (fun v _ => natCard_neighborSet_graphOf 𝓖 h2 v)

end Work.Deep.GKO
