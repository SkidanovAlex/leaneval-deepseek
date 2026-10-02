import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs

namespace Work.Deep.Kahn

/-- **Double counting**: the total size of the edges of a finite hypergraph on
`Fin n` equals the sum of the degrees of its vertices.  Both sides count the
incidence `(v, e)` with `v ∈ e`.

The proof exhibits the two sides as the cardinality of the two "transposed"
sigma-finsets `Σ e, {v ∈ e}` and `Σ v, {e ∋ v}` and uses the swap bijection
between them (`Finset.card_bij'`). -/
theorem sum_edgeSize_eq_sum_degree {n : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗] :
    (∑ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)))
      = ∑ v : Fin n, ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v := by
  classical
  -- the degree of `v` is the number of edges of `𝓗` containing `v`
  have hdeg : ∀ v : Fin n,
      ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v
        = ((Finset.univ : Finset 𝓗).filter (fun e : 𝓗 => v ∈ (e : Set (Fin n)))).card := by
    intro v
    rw [ErdosFaberLovaszConjecture.hypergraphDegree, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  -- the left-hand side is the cardinality of the sigma-finset of vertices of edges
  have hL : (∑ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)))
      = (((Finset.univ : Finset 𝓗).sigma
          (fun e : 𝓗 => ErdosFaberLovaszConjecture.verts (e : Set (Fin n)))).card) := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun e _ => rfl)
  -- the right-hand side is the cardinality of the sigma-finset of edges through vertices
  have hR : (∑ v : Fin n, ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v)
      = (((Finset.univ : Finset (Fin n)).sigma
          (fun v : Fin n => (Finset.univ : Finset 𝓗).filter
            (fun e : 𝓗 => v ∈ (e : Set (Fin n))))).card) := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun v _ => hdeg v)
  rw [hL, hR]
  -- the two sigma-finsets are exchanged by the swap of the components
  refine Finset.card_bij' (fun p _ => ⟨p.2, p.1⟩) (fun q _ => ⟨q.2, q.1⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter,
      ErdosFaberLovaszConjecture.mem_verts] at hp ⊢
    exact hp
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter,
      ErdosFaberLovaszConjecture.mem_verts] at hq ⊢
    exact hq
  · intro p hp
    cases p with
    | mk e v => rfl
  · intro q hq
    cases q with
    | mk v e => rfl

end Work.Deep.Kahn
