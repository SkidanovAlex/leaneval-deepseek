import Submission.EFL.MultiHypergraph

/-!
# Degrees of families of edges

Elementary facts about the degree `d_𝓕(w) = |{e ∈ 𝓕 : w ∈ e}|` of a vertex in a
family of edges, used in the proof of the Regularising Lemma 11.3:

* `hdeg`,`hdeg_sdiff`, `hdeg_union` — additivity of degrees;
* `hdeg_eq_degAt` — for a family of 2-element sets, the number of edges
  containing `w` equals the size of its neighbourhood `N_R(w)`;
* `notMem_nbrs_self`, `degAt_le_pred` — a vertex is not adjacent to itself and
  `d_G(w) ≤ n - 1`;
* `hdeg_eq_small_add` — splitting the degree into small edges and edges of
  size `> r₁`.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

theorem hdeg_sdiff {𝓕 𝓗 : Hypergraph (Fin n)} (h : 𝓕 ⊆ 𝓗) (w : Fin n) :
    MultiHypergraph.hdeg (𝓗 \ 𝓕) w =
      MultiHypergraph.hdeg 𝓗 w - MultiHypergraph.hdeg 𝓕 w := by
  have hset : {e ∈ 𝓗 \ 𝓕 | w ∈ e} = {e ∈ 𝓗 | w ∈ e} \ {e ∈ 𝓕 | w ∈ e} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    tauto
  have hsub : {e ∈ 𝓕 | w ∈ e} ⊆ {e ∈ 𝓗 | w ∈ e} := by
    intro e he
    exact ⟨h he.1, he.2⟩
  rw [MultiHypergraph.hdeg, hset, Set.ncard_sdiff hsub]
  rfl

theorem hdeg_union {𝓕 𝓖 : Hypergraph (Fin n)} (h : Disjoint 𝓕 𝓖) (w : Fin n) :
    MultiHypergraph.hdeg (𝓕 ∪ 𝓖) w = MultiHypergraph.hdeg 𝓕 w + MultiHypergraph.hdeg 𝓖 w := by
  have hset : {e ∈ 𝓕 ∪ 𝓖 | w ∈ e} = {e ∈ 𝓕 | w ∈ e} ∪ {e ∈ 𝓖 | w ∈ e} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_union]
    tauto
  have hdisj : Disjoint {e ∈ 𝓕 | w ∈ e} {e ∈ 𝓖 | w ∈ e} := by
    rw [Set.disjoint_left]
    intro e h1 h2
    exact Set.disjoint_left.mp h h1.1 h2.1
  rw [MultiHypergraph.hdeg, hset, Set.ncard_union_eq hdisj]
  rfl

/-- The degree of `w` in a family all of whose edges have two elements equals
the size of the neighbourhood `N_R(w)`. -/
theorem hdeg_eq_degAt (R : Hypergraph (Fin n)) (hR : ∀ e ∈ R, e.ncard = 2) (w : Fin n) :
    MultiHypergraph.hdeg R w = degAt R w := by
  have hex : ∀ e : Set (Fin n), e ∈ R → w ∈ e → ∃ x : Fin n, x ∈ e ∧ x ≠ w := by
    intro e heR hew
    have h2 : e.ncard = 2 := hR e heR
    have h1 : (e \ ({w} : Set (Fin n))).ncard = 1 := by
      rw [Set.ncard_sdiff (by simpa using hew), Set.ncard_singleton, h2]
    have hpos : 0 < (e \ ({w} : Set (Fin n))).ncard := by omega
    obtain ⟨x, hx⟩ :=
      (Set.ncard_pos (s := e \ ({w} : Set (Fin n))) (Set.toFinite _)).mp hpos
    exact ⟨x, hx.1, hx.2⟩
  have hspec : ∀ (e : Set (Fin n)) (he : e ∈ R) (hew : w ∈ e),
      ({w, Classical.choose (hex e he hew)} : Set (Fin n)) = e := by
    intro e he hew
    obtain ⟨h1, h2⟩ := Classical.choose_spec (hex e he hew)
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro y hy
      rcases (by simpa using hy : y = w ∨ y = Classical.choose (hex e he hew)) with rfl | rfl
      · exact hew
      · exact h1
    · rw [hR e he, Set.ncard_pair (Ne.symm h2)]
  refine Set.ncard_congr (fun e he => Classical.choose (hex e he.1 he.2)) ?_ ?_ ?_
  · intro e he
    show Classical.choose (hex e he.1 he.2) ∈ nbrs R w
    show ({w, Classical.choose (hex e he.1 he.2)} : Set (Fin n)) ∈ R
    rw [hspec e he.1 he.2]
    exact he.1
  · intro e e' he he' heq
    rw [← hspec e he.1 he.2, ← hspec e' he'.1 he'.2, heq]
  · intro x hx
    have hxR : ({w, x} : Set (Fin n)) ∈ R := hx
    have hw1 : w ∈ ({w, x} : Set (Fin n)) := by simp
    refine ⟨({w, x} : Set (Fin n)), ⟨hxR, hw1⟩, ?_⟩
    obtain ⟨hc1, hc2⟩ := Classical.choose_spec (hex ({w, x}) hxR hw1)
    have hmem : Classical.choose (hex ({w, x}) hxR hw1) ∈ ({w, x} : Set (Fin n)) := hc1
    rcases (by simpa using hmem : Classical.choose (hex ({w, x}) hxR hw1) = w ∨
      Classical.choose (hex ({w, x}) hxR hw1) = x) with h' | h'
    · exact absurd h' hc2
    · exact h'

/-- A vertex is not adjacent to itself in a family of 2-element edges. -/
theorem notMem_nbrs_self (R : Hypergraph (Fin n)) (hR : ∀ e ∈ R, e.ncard = 2) (w : Fin n) :
    w ∉ nbrs R w := by
  intro h
  have hh : ({w, w} : Set (Fin n)) ∈ R := h
  have h' : ({w} : Set (Fin n)) ∈ R := by
    rwa [show ({w, w} : Set (Fin n)) = ({w} : Set (Fin n)) from by simp] at hh
  have h2 := hR ({w} : Set (Fin n)) h'
  rw [Set.ncard_singleton] at h2
  omega

/-- The degree of a vertex in a family of 2-element edges is at most `n - 1`. -/
theorem degAt_le_pred (R : Hypergraph (Fin n)) (hR : ∀ e ∈ R, e.ncard = 2) (w : Fin n) :
    degAt R w ≤ n - 1 := by
  have hsub : nbrs R w ⊆ (Set.univ : Set (Fin n)) \ {w} := by
    intro x hx
    exact ⟨Set.mem_univ x, fun hxw => notMem_nbrs_self R hR w (hxw ▸ hx)⟩
  have h1 : (nbrs R w).ncard ≤ ((Set.univ : Set (Fin n)) \ {w}).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((Set.univ : Set (Fin n)) \ {w}).ncard = n - 1 := by
    rw [Set.ncard_sdiff (Set.subset_univ _), Set.ncard_singleton, Set.ncard_univ,
      Nat.card_fin]
  calc degAt R w = (nbrs R w).ncard := rfl
    _ ≤ ((Set.univ : Set (Fin n)) \ {w}).ncard := h1
    _ = n - 1 := h2

/-- Splitting a degree into the edges of size at most `r₁` and the remaining
edges. -/
theorem hdeg_eq_small_add (𝓗 : Hypergraph (Fin n)) (r₁ : ℕ) (w : Fin n) :
    MultiHypergraph.hdeg 𝓗 w =
      MultiHypergraph.hdeg (𝓗.smallEdges r₁) w +
        {e ∈ 𝓗 | w ∈ e ∧ r₁ < e.ncard}.ncard := by
  have hset : {e ∈ 𝓗 | w ∈ e} =
      {e ∈ 𝓗.smallEdges r₁ | w ∈ e} ∪ {e ∈ 𝓗 | w ∈ e ∧ r₁ < e.ncard} := by
    ext e
    constructor
    · intro he
      by_cases hr : e.ncard ≤ r₁
      · exact Or.inl ⟨⟨he.1, by rwa [edgeSize_eq_ncard]⟩, he.2⟩
      · exact Or.inr ⟨he.1, he.2, not_le.mp hr⟩
    · intro he
      rcases he with h1 | h2
      · exact ⟨((mem_smallEdges 𝓗 r₁ e).mp h1.1).1, h1.2⟩
      · exact ⟨h2.1, h2.2.1⟩
  have hdisj : Disjoint {e ∈ 𝓗.smallEdges r₁ | w ∈ e} {e ∈ 𝓗 | w ∈ e ∧ r₁ < e.ncard} := by
    rw [Set.disjoint_left]
    intro e h1 h2
    have h3 : edgeSize e ≤ r₁ := ((mem_smallEdges 𝓗 r₁ e).mp h1.1).2
    rw [edgeSize_eq_ncard] at h3
    have h4 : r₁ < e.ncard := h2.2.2
    omega
  rw [MultiHypergraph.hdeg, hset, Set.ncard_union_eq hdisj]
  rfl

end

end ErdosFaberLovaszConjecture
