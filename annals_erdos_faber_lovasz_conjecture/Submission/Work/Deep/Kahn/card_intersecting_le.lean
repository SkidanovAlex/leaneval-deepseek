import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs

set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

/-- **Neighbours of an edge.**  The number of edges `f ≠ e₀` of `𝓗` meeting `e₀`
is at most `∑_{v ∈ e₀} (d(v) - 1)`: every such edge contains a vertex `v` of
`e₀`, and there are `d(v) - 1` edges other than `e₀` through `v` (the edge `e₀`
itself is one of the `d(v)` edges through `v`). -/
theorem card_intersecting_le {n : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (e₀ : 𝓗) :
    Nat.card {f : 𝓗 // f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ (e₀ : Set (Fin n))).Nonempty} ≤
      ∑ v ∈ ErdosFaberLovaszConjecture.verts (e₀ : Set (Fin n)),
        (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v - 1) := by
  classical
  haveI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  -- the vertex set of `e₀`
  set E₀ : Set (Fin n) := (e₀ : Set (Fin n)) with hE₀
  -- the edges `≠ e₀` meeting `e₀`
  set S : Finset 𝓗 := (Finset.univ : Finset 𝓗).filter
    (fun f : 𝓗 => f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ E₀).Nonempty) with hS
  -- the edges `≠ e₀` containing the vertex `v`
  set C : Fin n → Finset 𝓗 := fun v => (Finset.univ : Finset 𝓗).filter
    (fun f : 𝓗 => f ≠ e₀ ∧ v ∈ (f : Set (Fin n))) with hC
  -- the degree of a vertex is the number of edges through it
  have hdeg : ∀ v : Fin n, ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v =
      ((Finset.univ : Finset 𝓗).filter (fun f : 𝓗 => v ∈ (f : Set (Fin n)))).card := by
    intro v
    rw [ErdosFaberLovaszConjecture.hypergraphDegree, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  -- the intersection count is the cardinality of `S`
  have hLHS : Nat.card {f : 𝓗 // f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ E₀).Nonempty} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hS]
  -- `S` is the union of the `C v` over the vertices `v` of `e₀`
  have hSuni : S = (ErdosFaberLovaszConjecture.verts E₀).biUnion C := by
    rw [hS, hC]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      ErdosFaberLovaszConjecture.mem_verts]
    constructor
    · rintro ⟨hne, v, hv⟩
      exact ⟨v, hv.2, hne, hv.1⟩
    · rintro ⟨v, hvE, hne, hvf⟩
      exact ⟨hne, v, hvf, hvE⟩
  -- each `C v` has `d v - 1` elements, because `e₀` is one of the edges through `v`
  have hcard : ∀ v ∈ ErdosFaberLovaszConjecture.verts E₀,
      (C v).card = ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v - 1 := by
    intro v hv
    have hvE : v ∈ E₀ := (ErdosFaberLovaszConjecture.mem_verts E₀ v).mp hv
    have hmem : e₀ ∈ (Finset.univ : Finset 𝓗).filter
        (fun f : 𝓗 => v ∈ (f : Set (Fin n))) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ e₀, hvE⟩
    have hCe : C v = ((Finset.univ : Finset 𝓗).filter
        (fun f : 𝓗 => v ∈ (f : Set (Fin n)))).erase e₀ := by
      rw [hC]
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hCe, Finset.card_erase_of_mem hmem, hdeg v]
  calc Nat.card {f : 𝓗 // f ≠ e₀ ∧ ((f : Set (Fin n)) ∩ E₀).Nonempty}
      = S.card := hLHS
    _ = ((ErdosFaberLovaszConjecture.verts E₀).biUnion C).card := by rw [hSuni]
    _ ≤ ∑ v ∈ ErdosFaberLovaszConjecture.verts E₀, (C v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ ErdosFaberLovaszConjecture.verts E₀,
          (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v - 1) :=
        Finset.sum_congr rfl (fun v hv => hcard v hv)

end Work.Deep.Kahn
