import Submission.EFL.LineGraph
import Submission.EFL.DeepInputs
import Submission.EFL.Comm.InternalMatchingConnect
import Submission.Commons.Combinatorics.Hypergraph.eq_univ_pairs_of_degree
import Submission.Commons.Combinatorics.Finset.set_pair_partition
import Submission.Commons.Combinatorics.SimpleGraph.perfectMatching_or_card_le_four

/-!
# §7.4: absorption for difficult matchings (Lemma 7.12)

This module formalises the paper's Lemma `difficult-edge-absorption`: if `𝓗` is
a linear hypergraph without singleton edges and `e` is a *huge* edge, then
either `{e}` can be extended (using edges of the 2-shadow `G = 𝓗^{(2)}`) to a
matching covering every vertex of `V^{(n-1)}(𝓗)` and all but at most five
vertices of `V^{(n-2)}(𝓗)`, or `χ'(𝓗) ≤ n`.

The proof has three ingredients: the structural facts

* a vertex of degree `n-1` in `𝓗` is joined by a 2-edge to every other vertex,
* a vertex of degree `n-2` has at most two non-neighbours,
* no vertex of a huge edge has degree `n-1` or `n-2`,

the pairing construction (`set_pair_partition`), and the graph-theoretic input
`perfectMatching_or_card_le_four` applied to the 2-shadow induced on
`V^{(n-1)}(𝓗) ∪ V^{(n-2)}(𝓗)`; in the exceptional case (no perfect matching and
at most four vertices) the remaining colouring is obtained from the two-max
form of Vizing's theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## The margins and the degree classes -/

/-- The numeric margins of Lemma 7.12: `0 < 1/n₀ ≪ β ≪ 1`, in the concrete
form used below (`16 ≤ βn`, which makes every *huge* edge have at least four
vertices). -/
structure DiffMargins (n : ℕ) (β : ℝ) : Prop where
  hβ : 0 < β
  hβ1 : β ≤ 1
  hn : 16 ≤ β * (n : ℝ)

/-- `V^{(d)}(𝓗)`: the vertices of `𝓗` of degree exactly `d`. -/
def Vdeg (𝓗 : Hypergraph (Fin n)) (d : ℕ) : Set (Fin n) :=
  {v | ({f : Set (Fin n) | f ∈ 𝓗 ∧ v ∈ f} : Set (Set (Fin n))).ncard = d}

/-- Every edge of `𝓗` has at least two vertices, phrased with `Set.ncard`. -/
theorem two_le_ncard_of_mem {𝓗 : Hypergraph (Fin n)} (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard)
    {f : Set (Fin n)} (hf : f ∈ 𝓗) : 2 ≤ f.ncard := hno f hf

/-! ## Pairing constructions -/

/-- **Pairing of an even vertex set.**  If every pair of distinct vertices of
`A` is an edge of `𝓗`, then there is a matching of `𝓗` whose edges are the pairs
inside `A` and which covers `A`. -/
theorem exists_matching_covering_of_pairs {𝓗 : Hypergraph (Fin n)} {A : Set (Fin n)}
    (heven : Even A.ncard)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → ({u, v} : Set (Fin n)) ∈ 𝓗) :
    ∃ M1 : Set 𝓗, IsMatching 𝓗 M1 ∧ Covers M1 A ∧
      (∀ f ∈ M1, (f : Set (Fin n)) ⊆ A) ∧ (∀ f ∈ M1, edgeSize (f : Set (Fin n)) = 2) := by
  classical
  obtain ⟨P, hPsub, hPpair, hPcov, hPdisj⟩ :=
    Commons.Combinatorics.Finset.set_pair_partition (V := Fin n) A heven
  have hPmem : ∀ p ∈ P, p ∈ 𝓗 := by
    intro p hp
    obtain ⟨u, hu, v, hv, huv, rfl⟩ := hPpair p hp
    exact hpair u hu v hv huv
  refine ⟨{f : 𝓗 | (f : Set (Fin n)) ∈ P}, ?_, ?_, ?_, ?_⟩
  · intro f₁ hf₁ f₂ hf₂ hne
    exact hPdisj hf₁ hf₂ (fun h => hne (Subtype.ext h))
  · intro x hx
    rw [mem_matchVert]
    obtain ⟨p, hp, hxp⟩ := hPcov x hx
    exact ⟨⟨p, hPmem p hp⟩, hp, hxp⟩
  · intro f hf
    exact hPsub f.1 hf
  · intro f hf
    obtain ⟨u, hu, v, hv, huv, hfu⟩ := hPpair f.1 hf
    rw [hfu, edgeSize_eq_ncard, Set.ncard_pair huv]

/-- **Pairing of an odd vertex set with an outside partner.**  If every pair of
distinct vertices of `A` is an edge of `𝓗`, `A` has odd cardinality, `y ∉ A` and
`{u,y} ∈ 𝓗` for every `u ∈ A`, then there is a matching whose edges are the pairs
of `A ∖ {u₀}` together with `{u₀,y}` and which covers `A`. -/
theorem exists_matching_covering_of_pairs_odd {𝓗 : Hypergraph (Fin n)} {A : Set (Fin n)}
    {y : Fin n} (hodd : Odd A.ncard) (hy : y ∉ A)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → ({u, v} : Set (Fin n)) ∈ 𝓗)
    (hyadj : ∀ u ∈ A, ({u, y} : Set (Fin n)) ∈ 𝓗) :
    ∃ M1 : Set 𝓗, IsMatching 𝓗 M1 ∧ Covers M1 A ∧
      (∀ f ∈ M1, (f : Set (Fin n)) ⊆ A ∪ {y}) ∧ (∀ f ∈ M1, edgeSize (f : Set (Fin n)) = 2) := by
  classical
  have hne : ∃ u : Fin n, u ∈ A := by
    rcases Set.eq_empty_or_nonempty A with h | h
    · rw [h] at hodd
      simp at hodd
    · exact h
  obtain ⟨u₀, hu₀A⟩ := hne
  have hcard' : (A \ {u₀}).ncard + 1 = A.ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hu₀A]
    rcases hodd with ⟨m, hm⟩
    omega
  have heven : Even (A \ {u₀}).ncard := by
    rcases hodd with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  obtain ⟨M1, hmat, hcov, hsub, hsz⟩ :=
    exists_matching_covering_of_pairs (𝓗 := 𝓗) heven
      (fun u hu v hv huv => hpair u (Set.sdiff_subset hu) v (Set.sdiff_subset hv) huv)
  have hyu₀ : y ≠ u₀ := fun h => hy (h ▸ hu₀A)
  set e0 : 𝓗 := ⟨({u₀, y} : Set (Fin n)), hyadj u₀ hu₀A⟩ with he0def
  refine ⟨M1 ∪ {e0}, ?_, ?_, ?_, ?_⟩
  · refine isMatching_union hmat (isMatching_singleton 𝓗 e0) ?_
    rw [Set.disjoint_left]
    intro x hx hxM
    rw [mem_matchVert] at hx hxM
    obtain ⟨g, hg, hxg⟩ := hx
    obtain ⟨g', hg', hxg'⟩ := hxM
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    have hx1 : x ∈ (e0 : Set (Fin n)) := hxg'
    have hx2 : x ∈ (g : Set (Fin n)) := hxg
    have hgA : x ∈ A \ {u₀} := hsub g hg hx2
    rw [he0def] at hx1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1
    rcases hx1 with rfl | rfl
    · exact (Set.mem_sdiff x).mp hgA |>.2 rfl
    · exact hy hgA.1
  · intro x hx
    by_cases hxu : x = u₀
    · subst hxu
      rw [mem_matchVert]
      exact ⟨e0, Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl), by
        rw [he0def]; simp⟩
    · obtain ⟨f, hf, hxf⟩ := (mem_matchVert (M := M1) (x := x)).mp (hcov ⟨hx, hxu⟩)
      rw [mem_matchVert]
      exact ⟨f, Set.mem_union_left _ hf, hxf⟩
  · intro f hf
    rw [Set.mem_union] at hf
    rcases hf with hf | hf
    · intro z hz
      exact Or.inl (hsub f hf hz).1
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      intro z hz
      rw [he0def] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hu₀A
      · exact Or.inr rfl
  · intro f hf
    rw [Set.mem_union, Set.mem_singleton_iff] at hf
    rcases hf with hf | hf
    · exact hsz f hf
    · subst hf
      rw [he0def, edgeSize_eq_ncard, Set.ncard_pair (Ne.symm hyu₀)]

end

end ErdosFaberLovaszConjecture
