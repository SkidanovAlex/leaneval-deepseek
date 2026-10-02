import Submission.EFL.DiffAbs
import Submission.Commons.Combinatorics.Hypergraph.ncard_notAdj_le_two_of_degree
import Submission.Commons.Combinatorics.Hypergraph.huge_edge_disjoint_high_degree
import Submission.EFL.Comm.EdgeColoringPairFamily

/-!
# §7.4: absorption for difficult matchings (Lemma 7.12)

`DiffAbs.lean` contains the basic pairing constructions; this module proves the
paper's Lemma `difficult-edge-absorption`: if `𝓗` is a linear hypergraph without
singleton edges and `e` is a *huge* edge, then either `{e}` extends (using edges
of the 2-shadow `G = 𝓗^{(2)}`) to a matching covering every vertex of
`V^{(n-1)}(𝓗)` and all but at most five vertices of `V^{(n-2)}(𝓗)`, or
`χ'(𝓗) ≤ n`.

The structural input `huge_edge_disjoint_high_degree` (no vertex of a huge edge
has degree `n-1` or `n-2`), the non-neighbour bound
`ncard_notAdj_le_two_of_degree` and the two-max Vizing input
`edgeColoring_of_pairFamily_two_max` are proved in the shared commons; the
graph-theoretic input `perfectMatching_or_card_le_four` decides whether the
2-shadow on `V^{(n-1)} ∪ V^{(n-2)}` has a perfect matching.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}
variable {β : ℝ}

/-! ## Basic structural facts -/

/-- Membership in the vertex set of a singleton family. -/
theorem mem_matchVert_singleton {𝓗 : Hypergraph (Fin n)} {f : 𝓗} {x : Fin n} :
    x ∈ matchVert ({f} : Set 𝓗) ↔ x ∈ (f : Set (Fin n)) := by
  rw [mem_matchVert]
  constructor
  · rintro ⟨g, hg, hxg⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hxg
  · intro hx
    exact ⟨f, Set.mem_singleton f, hx⟩

/-- `{v,w} ∈ 𝓗.pow2` for a `2`-edge family. -/
theorem mem_pow2_of_pair {𝓗 : Hypergraph (Fin n)} {u v : Fin n} (huv : u ≠ v)
    (h : ({u, v} : Set (Fin n)) ∈ 𝓗) : ({u, v} : Set (Fin n)) ∈ 𝓗.pow2 :=
  mem_pow2.mpr ⟨h, by rw [edgeSize_eq_ncard, Set.ncard_pair huv]⟩

/-! ## A perfect matching of `graphOf` gives a matching family -/

/-- A perfect matching of the 2-graph `graphOf R W` yields a matching of `𝓗`
covering `W`, all of whose edges lie in `R` and inside `W`. -/
theorem exists_matching_of_perfectMatching {𝓗 R : Hypergraph (Fin n)} (hRsub : R ⊆ 𝓗)
    {W : Set (Fin n)} {hR2 : ∀ f ∈ R, edgeSize f = 2}
    {M : (graphOf R W hR2).Subgraph} (hM : M.IsPerfectMatching) :
    ∃ M1 : Set 𝓗, IsMatching 𝓗 M1 ∧ Covers M1 W ∧
      (∀ f ∈ M1, (f : Set (Fin n)) ∈ R) ∧ (∀ f ∈ M1, (f : Set (Fin n)) ⊆ W) := by
  classical
  have huniq : ∀ v : ↥W, ∃! w, M.Adj v w := (SimpleGraph.Subgraph.isPerfectMatching_iff).mp hM
  set φ : ↥W → ↥W := fun v => Classical.choose (huniq v) with hφdef
  have hφ1 : ∀ v, M.Adj v (φ v) := fun v => (Classical.choose_spec (huniq v)).1
  have hφ2 : ∀ v w, M.Adj v w → w = φ v := fun v w h => (Classical.choose_spec (huniq v)).2 w h
  have hinv : ∀ v, φ (φ v) = v := fun v => (hφ2 (φ v) v (hφ1 v).symm).symm
  have hedge : ∀ v : ↥W, ({v.1, (φ v).1} : Set (Fin n)) ∈ R := fun v => (hφ1 v).adj_sub
  have horbit : ∀ (e₁ e₂ : Set (Fin n)) (v₁ v₂ : ↥W),
      e₁ = ({v₁.1, (φ v₁).1} : Set (Fin n)) → e₂ = ({v₂.1, (φ v₂).1} : Set (Fin n)) →
      (e₁ ∩ e₂).Nonempty → e₁ = e₂ := by
    rintro e₁ e₂ v₁ v₂ rfl rfl ⟨x, hx1, hx2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
    have key : v₁ = v₂ ∨ v₁ = φ v₂ := by
      rcases hx1 with h1 | h1 <;> rcases hx2 with h2 | h2
      · exact Or.inl (Subtype.ext (h1.symm.trans h2))
      · exact Or.inr (Subtype.ext (h1.symm.trans h2))
      · refine Or.inr ?_
        have h3 : φ v₁ = v₂ := Subtype.ext (h1.symm.trans h2)
        rw [← hinv v₁, h3]
      · refine Or.inl ?_
        have h3 : φ v₁ = φ v₂ := Subtype.ext (h1.symm.trans h2)
        rw [← hinv v₁, ← hinv v₂, h3]
    rcases key with h | h
    · rw [h]
    · rw [h, hinv v₂, Set.pair_comm]
  set M1 : Set 𝓗 := {g : 𝓗 | ∃ v : ↥W, (g : Set (Fin n)) = ({v.1, (φ v).1} : Set (Fin n))}
    with hM1def
  have hM1mem : ∀ v : ↥W, (⟨({v.1, (φ v).1} : Set (Fin n)), hRsub (hedge v)⟩ : 𝓗) ∈ M1 :=
    fun v => ⟨v, rfl⟩
  refine ⟨M1, ?_, ?_, ?_, ?_⟩
  · intro g₁ hg₁ g₂ hg₂ hne
    obtain ⟨v₁, hv₁⟩ := hg₁
    obtain ⟨v₂, hv₂⟩ := hg₂
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hne (Subtype.ext (horbit _ _ v₁ v₂ hv₁ hv₂ ⟨x, hx, hx'⟩))
  · intro w hw
    rw [mem_matchVert]
    exact ⟨⟨({w, (φ ⟨w, hw⟩).1} : Set (Fin n)), hRsub (hedge ⟨w, hw⟩)⟩, hM1mem ⟨w, hw⟩,
      Set.mem_insert _ _⟩
  · intro g hg
    obtain ⟨v, hv⟩ := hg
    rw [hv]
    exact hedge v
  · intro g hg
    obtain ⟨v, hv⟩ := hg
    rw [hv]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | rfl
    · exact v.2
    · exact (φ v).2


/-! ## Structural facts about the degree classes -/

/-- `e` is disjoint from the vertices of degree `n-1` and of degree `n-2`. -/
theorem disjoint_e_Vdeg {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) (he : e ∈ 𝓗) (he4 : 4 ≤ e.ncard)
    {v : Fin n} (hv : v ∈ e) : v ∉ Vdeg 𝓗 (n - 1) ∧ v ∉ Vdeg 𝓗 (n - 2) := by
  constructor
  · intro hv1
    exact Commons.Combinatorics.Hypergraph.huge_edge_disjoint_high_degree 𝓗 hlin hno he he4 hv
      (Or.inl (by simpa [Vdeg] using hv1))
  · intro hv2
    exact Commons.Combinatorics.Hypergraph.huge_edge_disjoint_high_degree 𝓗 hlin hno he he4 hv
      (Or.inr (by simpa [Vdeg] using hv2))

/-- The vertices of degree `n-1` are joined to every other vertex by an edge. -/
theorem pairs_of_Vdeg_one {𝓗 : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard)
    {v : Fin n} (hv : v ∈ Vdeg 𝓗 (n - 1)) (w : Fin n) (hw : w ≠ v) :
    ({v, w} : Set (Fin n)) ∈ 𝓗 :=
  Commons.Combinatorics.Hypergraph.eq_univ_pairs_of_degree (Fin n) 𝓗 hlin hno
    (by simpa [Vdeg] using hv) w hw

/-- A vertex of degree `n-2` has at most two non-neighbours. -/
theorem notAdj_le_two_of_Vdeg_two {𝓗 : Hypergraph (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard)
    {v : Fin n} (hv : v ∈ Vdeg 𝓗 (n - 2)) :
    {w : Fin n | w ≠ v ∧ ({v, w} : Set (Fin n)) ∉ 𝓗}.ncard ≤ 2 :=
  Commons.Combinatorics.Hypergraph.ncard_notAdj_le_two_of_degree (Fin n) 𝓗 hlin hno (by simpa [Vdeg] using hv)

/-! ## The extension in the case `U₂ = ∅` -/

/-- **Case `U₂ = ∅`, even `|U₁|`.** -/
theorem exists_extension_even {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) (he : e ∈ 𝓗) (he4 : 4 ≤ e.ncard)
    (hU2 : Vdeg 𝓗 (n - 2) = ∅) (heven : Even (Vdeg 𝓗 (n - 1)).ncard) :
    ∃ M' : Set 𝓗, ({⟨e, he⟩} : Set 𝓗) ⊆ M' ∧ IsMatching 𝓗 M' ∧
      (∀ f ∈ M', f ≠ ⟨e, he⟩ → (f : Set (Fin n)) ∈ 𝓗.pow2) ∧
      Covers M' (Vdeg 𝓗 (n - 1)) ∧
      ((Vdeg 𝓗 (n - 2) \ matchVert M').ncard ≤ 5) := by
  classical
  have hpair : ∀ u ∈ Vdeg 𝓗 (n - 1), ∀ v ∈ Vdeg 𝓗 (n - 1), u ≠ v →
      ({u, v} : Set (Fin n)) ∈ 𝓗 :=
    fun u hu v _ huv => pairs_of_Vdeg_one hlin hno hu v (fun h => huv h.symm)
  obtain ⟨M1, hmat, hcov, hsub, hsz⟩ := exists_matching_covering_of_pairs heven hpair
  have hdisj : Disjoint (matchVert ({⟨e, he⟩} : Set 𝓗)) (matchVert M1) := by
    rw [Set.disjoint_left]
    intro x hx hxM
    rw [mem_matchVert_singleton] at hx
    rw [mem_matchVert] at hxM
    obtain ⟨g, hg, hxg⟩ := hxM
    exact (disjoint_e_Vdeg hlin hno he he4 hx).1 (hsub g hg hxg)
  refine ⟨({⟨e, he⟩} : Set 𝓗) ∪ M1, (fun x hx => Or.inl hx), ?_, ?_, ?_, ?_⟩
  · exact isMatching_union (isMatching_singleton 𝓗 ⟨e, he⟩) hmat hdisj
  · intro f hf hfne
    rw [Set.mem_union] at hf
    rcases hf with hf | hf
    · rw [Set.mem_singleton_iff] at hf
      exact absurd hf hfne
    · exact mem_pow2.mpr ⟨f.2, hsz f hf⟩
  · intro x hx
    rw [matchVert_union]
    exact Or.inr (hcov hx)
  · rw [hU2]
    simp

/-- **Case `U₂ = ∅`, `|U₁|` odd, with a vertex `y` outside `e ∪ U₁`.** -/
theorem exists_extension_odd {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) (he : e ∈ 𝓗) (he4 : 4 ≤ e.ncard)
    (hU2 : Vdeg 𝓗 (n - 2) = ∅) (hodd : Odd (Vdeg 𝓗 (n - 1)).ncard)
    {y : Fin n} (hyU : y ∉ Vdeg 𝓗 (n - 1)) (hye : y ∉ e) :
    ∃ M' : Set 𝓗, ({⟨e, he⟩} : Set 𝓗) ⊆ M' ∧ IsMatching 𝓗 M' ∧
      (∀ f ∈ M', f ≠ ⟨e, he⟩ → (f : Set (Fin n)) ∈ 𝓗.pow2) ∧
      Covers M' (Vdeg 𝓗 (n - 1)) ∧
      ((Vdeg 𝓗 (n - 2) \ matchVert M').ncard ≤ 5) := by
  classical
  have hpair : ∀ u ∈ Vdeg 𝓗 (n - 1), ∀ v ∈ Vdeg 𝓗 (n - 1), u ≠ v →
      ({u, v} : Set (Fin n)) ∈ 𝓗 :=
    fun u hu v _ huv => pairs_of_Vdeg_one hlin hno hu v (fun h => huv h.symm)
  have hyadj : ∀ u ∈ Vdeg 𝓗 (n - 1), ({u, y} : Set (Fin n)) ∈ 𝓗 := by
    intro u hu
    exact pairs_of_Vdeg_one hlin hno hu y (fun h => hyU (h ▸ hu))
  obtain ⟨M1, hmat, hcov, hsub, hsz⟩ :=
    exists_matching_covering_of_pairs_odd hodd hyU hpair hyadj
  have hdisj : Disjoint (matchVert ({⟨e, he⟩} : Set 𝓗)) (matchVert M1) := by
    rw [Set.disjoint_left]
    intro x hx hxM
    rw [mem_matchVert_singleton] at hx
    rw [mem_matchVert] at hxM
    obtain ⟨g, hg, hxg⟩ := hxM
    have hxg' : x ∈ Vdeg 𝓗 (n - 1) ∪ ({y} : Set (Fin n)) := hsub g hg hxg
    rw [Set.mem_union, Set.mem_singleton_iff] at hxg'
    rcases hxg' with hxg' | rfl
    · exact (disjoint_e_Vdeg hlin hno he he4 hx).1 hxg'
    · exact hye hx
  refine ⟨({⟨e, he⟩} : Set 𝓗) ∪ M1, (fun x hx => Or.inl hx), ?_, ?_, ?_, ?_⟩
  · exact isMatching_union (isMatching_singleton 𝓗 ⟨e, he⟩) hmat hdisj
  · intro f hf hfne
    rw [Set.mem_union] at hf
    rcases hf with hf | hf
    · rw [Set.mem_singleton_iff] at hf
      exact absurd hf hfne
    · exact mem_pow2.mpr ⟨f.2, hsz f hf⟩
  · intro x hx
    rw [matchVert_union]
    exact Or.inr (hcov hx)
  · rw [hU2]
    simp


/-! ## The exceptional colouring branch -/

/-- Two distinct elements of a set of cardinality at least two. -/
theorem exists_pair_of_two_le_ncard {V : Type*} [Fintype V] {s : Set V} (h : 2 ≤ s.ncard) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  by_contra hcon
  push_neg at hcon
  have h1 := (Set.ncard_le_one (s := s) (hs := Set.toFinite s)).mpr (fun a ha b hb => hcon a ha b hb)
  omega

/-- A `2`-element set containing `v` is `{v,x}` for some `x ≠ v`. -/
theorem eq_pair_of_ncard_two {s : Set (Fin n)} {v : Fin n} (hv : v ∈ s) (h2 : s.ncard = 2) :
    ∃ x : Fin n, x ≠ v ∧ s = ({v, x} : Set (Fin n)) := by
  have h1 : (s \ {v}).ncard = 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hv, h2]
  have hpos : 0 < (s \ {v}).ncard := by omega
  obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  have hxv : x ≠ v := fun h => hx.2 (by simpa [Set.mem_singleton_iff] using h)
  refine ⟨x, hxv, ?_⟩
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact hv
    · exact hx.1
  · rw [Set.ncard_pair (fun h => hxv h.symm), h2]

/-- `|V ∖ {v,x}| = n - 2`. -/
theorem ncard_compl_pair_eq {n : ℕ} (v x : Fin n) (h : v ≠ x) :
    (({v, x} : Set (Fin n))ᶜ).ncard = n - 2 := by
  have h3 := Set.ncard_compl_add_ncard ({v, x} : Set (Fin n)) (Set.toFinite _)
  rw [Set.ncard_pair h, Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

/-- `|V ∖ {v}| = n - 1`. -/
theorem ncard_compl_singleton_eq {n : ℕ} (v : Fin n) :
    (({v} : Set (Fin n))ᶜ).ncard = n - 1 := by
  have h3 := Set.ncard_compl_add_ncard ({v} : Set (Fin n)) (Set.toFinite _)
  rw [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

/-- The set of 2-shadow neighbours of `v` in a family `𝓡` of 2-edges. -/
def pairNbrs (𝓡 : Set (Set (Fin n))) (v : Fin n) : Set (Fin n) :=
  {x | x ≠ v ∧ ({v, x} : Set (Fin n)) ∈ 𝓡}

/-- **Case `U₂ = ∅`, `|U₁|` odd, and `V = e ∪ U₁`.**  Then `χ'(𝓗) ≤ n`. -/
theorem colorable_of_exceptional {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) (he : e ∈ 𝓗) (he4 : 4 ≤ e.ncard)
    (hU2 : Vdeg 𝓗 (n - 2) = ∅) (hodd : Odd (Vdeg 𝓗 (n - 1)).ncard)
    (hcover : ∀ v : Fin n, v ∈ e ∨ v ∈ Vdeg 𝓗 (n - 1)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  have hnU : e.ncard ≤ n := by
    have h := Set.ncard_le_ncard (Set.subset_univ e) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hn4 : 4 ≤ n := le_trans he4 hnU
  -- every edge other than `e` is a pair
  have hall : ∀ f ∈ 𝓗, f ≠ e → f.ncard = 2 := by
    intro f hf hfe
    have h2 : 2 ≤ f.ncard := hno f hf
    have h3 : f.ncard ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ f.ncard := by omega
      have hle : f.ncard ≤ (f ∩ e).ncard + (f ∩ Vdeg 𝓗 (n - 1)).ncard := by
        have hsplit : f ⊆ (f ∩ e) ∪ (f ∩ Vdeg 𝓗 (n - 1)) := by
          intro x hx
          rcases hcover x with hxe | hxU
          · exact Or.inl ⟨hx, hxe⟩
          · exact Or.inr ⟨hx, hxU⟩
        have h1 := Set.ncard_le_ncard hsplit (Set.toFinite _)
        have h2 := Set.ncard_union_le (f ∩ e) (f ∩ Vdeg 𝓗 (n - 1))
        omega
      rcases lt_or_ge (f ∩ e).ncard 2 with hA | hA
      · have hB : 2 ≤ (f ∩ Vdeg 𝓗 (n - 1)).ncard := by omega
        obtain ⟨u, hu, v, hv, huv⟩ := exists_pair_of_two_le_ncard hB
        have hpair := pairs_of_Vdeg_one hlin hno hu.2 v (fun h => huv h.symm)
        have hne : ({u, v} : Set (Fin n)) ≠ f := by
          intro hcon'
          have h2' : f.ncard = 2 := by rw [← hcon', Set.ncard_pair huv]
          omega
        have hsub2 := hlin (x := ({u, v} : Set (Fin n))) (y := f) hpair hf hne
        exact huv (hsub2 ⟨by simp, hu.1⟩ ⟨by simp, hv.1⟩)
      · have hB : 2 ≤ (f ∩ e).ncard := hA
        obtain ⟨u, hu, v, hv, huv⟩ := exists_pair_of_two_le_ncard hB
        have hsub2 := hlin (x := f) (y := e) hf he hfe
        exact huv (hsub2 ⟨hu.1, hu.2⟩ ⟨hv.1, hv.2⟩)
    omega
  -- pick `w ∈ U₁`
  obtain ⟨w, hwU⟩ : ∃ w : Fin n, w ∈ Vdeg 𝓗 (n - 1) := by
    rcases Set.eq_empty_or_nonempty (Vdeg 𝓗 (n - 1)) with h | h
    · rw [h] at hodd
      simp at hodd
    · exact h
  have heven : Even (Vdeg 𝓗 (n - 1) \ {w}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hwU]
    rcases hodd with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  have hpairU : ∀ u ∈ Vdeg 𝓗 (n - 1) \ {w}, ∀ v ∈ Vdeg 𝓗 (n - 1) \ {w}, u ≠ v →
      ({u, v} : Set (Fin n)) ∈ 𝓗 :=
    fun u hu v hv huv => pairs_of_Vdeg_one hlin hno hu.1 v (fun h => huv h.symm)
  obtain ⟨M1, hmat, hcov, hsub, hsz⟩ := exists_matching_covering_of_pairs heven hpairU
  set M1set : Set (Set (Fin n)) := {p | ∃ g ∈ M1, (g : Set (Fin n)) = p} with hM1set
  set 𝓗0 : Set (Set (Fin n)) := {p | p ∈ 𝓗 ∧ p ≠ e ∧ p ∉ M1set} with h𝓗0
  have hmem0 : ∀ p : Set (Fin n), p ∈ 𝓗0 ↔ p ∈ 𝓗 ∧ p ≠ e ∧ p ∉ M1set := by
    intro p
    rw [h𝓗0, Set.mem_ofPred_eq]
  have hR2_0 : ∀ p ∈ 𝓗0, p.ncard = 2 := fun p hp => hall p ((hmem0 p).mp hp).1 ((hmem0 p).mp hp).2.1
  have hD : ∀ v : Fin n, (pairNbrs 𝓗0 v).ncard ≤ n - 1 := by
    intro v
    have hsub' : pairNbrs 𝓗0 v ⊆ ({v}ᶜ : Set (Fin n)) := fun x hx => hx.1
    have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
    rwa [ncard_compl_singleton_eq v] at h1
  have hfew : {v : Fin n | (pairNbrs 𝓗0 v).ncard = n - 1}.ncard ≤ 2 := by
    have hsubw : {v : Fin n | (pairNbrs 𝓗0 v).ncard = n - 1} ⊆ ({w} : Set (Fin n)) := by
      intro v hv
      have hv' : (pairNbrs 𝓗0 v).ncard = n - 1 := hv
      by_contra hvw
      have hvw' : v ≠ w := fun h => hvw (Set.mem_singleton_iff.mpr h)
      have hx : ∃ x : Fin n, x ≠ v ∧ ({v, x} : Set (Fin n)) ∉ 𝓗0 := by
        by_cases hvU : v ∈ Vdeg 𝓗 (n - 1)
        · obtain ⟨g, hgM, hvg⟩ : ∃ g : 𝓗, g ∈ M1 ∧ v ∈ (g : Set (Fin n)) :=
            (mem_matchVert (M := M1) (x := v)).mp
              (hcov ⟨hvU, fun h => hvw' (Set.mem_singleton_iff.mp h)⟩)
          have hg2 : (g : Set (Fin n)).ncard = 2 := by
            have h := hsz g hgM
            rwa [edgeSize_eq_ncard] at h
          obtain ⟨x, hxv, hgx⟩ := eq_pair_of_ncard_two hvg hg2
          refine ⟨x, hxv, fun hcontra => ?_⟩
          have hmem : ({v, x} : Set (Fin n)) ∈ M1set := ⟨g, hgM, hgx⟩
          exact ((hmem0 _).mp hcontra).2.2 hmem
        · rcases hcover v with hve | hvU'
          · obtain ⟨x, hx⟩ : ∃ x, x ∈ e \ {v} := by
              have h1 : (e \ {v}).ncard = e.ncard - 1 :=
                Set.ncard_sdiff_singleton_of_mem hve
              exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)
            have hxv : x ≠ v := fun h => hx.2 (by simpa [Set.mem_singleton_iff] using h)
            refine ⟨x, hxv, fun hcontra => ?_⟩
            have hne : ({v, x} : Set (Fin n)) ≠ e := by
              intro h'
              have h2 : e.ncard = 2 := by rw [← h', Set.ncard_pair (fun h => hxv h.symm)]
              omega
            have hsub2 := hlin (x := ({v, x} : Set (Fin n))) (y := e)
              ((hmem0 _).mp hcontra).1 he hne
            exact hxv (hsub2 ⟨by simp, hve⟩ ⟨by simp, hx.1⟩).symm
          · exact absurd hvU' hvU
      obtain ⟨x, hxv, hxnot⟩ := hx
      have hsub2 : pairNbrs 𝓗0 v ⊆ ({v, x} : Set (Fin n))ᶜ := by
        intro y hy
        rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        push Not
        exact ⟨hy.1, fun h => hxnot (h ▸ hy.2)⟩
      have h1 := Set.ncard_le_ncard hsub2 (Set.toFinite _)
      rw [ncard_compl_pair_eq v x (Ne.symm hxv)] at h1
      omega
    have h1 := Set.ncard_le_ncard hsubw (Set.toFinite _)
    have h2 : (({w} : Set (Fin n))).ncard = 1 := Set.ncard_singleton w
    omega
  obtain ⟨col, hcol⟩ := Commons.Combinatorics.SimpleGraph.edgeColoring_of_pairFamily_two_max 𝓗0 hR2_0 (n - 1) hD hfew
  -- the matching `{e} ∪ M₁`
  have hdisjM : Disjoint (matchVert ({⟨e, he⟩} : Set 𝓗)) (matchVert M1) := by
    rw [Set.disjoint_left]
    intro z hz hzM
    rw [mem_matchVert_singleton] at hz
    rw [mem_matchVert] at hzM
    obtain ⟨g, hg, hzg⟩ := hzM
    exact (disjoint_e_Vdeg hlin hno he he4 hz).1 (hsub g hg hzg).1
  have hisM : IsMatching 𝓗 (({⟨e, he⟩} : Set 𝓗) ∪ M1) :=
    isMatching_union (isMatching_singleton 𝓗 ⟨e, he⟩) hmat hdisjM
  have hnot0 : ∀ g : 𝓗, (g : Set (Fin n)) ∉ 𝓗0 → g = ⟨e, he⟩ ∨ g ∈ M1 := by
    intro g hg
    by_contra hcon
    push Not at hcon
    refine hg ((hmem0 _).mpr ⟨g.2, fun h => hcon.1 (Subtype.ext h), fun h' => ?_⟩)
    obtain ⟨g', hg', heq⟩ := h'
    rw [Subtype.ext heq] at hg'
    exact hcon.2 hg'
  set fresh : Fin n := ⟨n - 1, by omega⟩ with hfresh
  have hcast : ∀ (c : Fin (n - 1)), Fin.castLE (by omega : n - 1 ≤ n) c ≠ fresh := by
    intro c hcon
    have h := congrArg Fin.val hcon
    simp only [Fin.castLE, hfresh, Fin.val_mk] at h
    have := c.isLt
    omega
  let lab : 𝓗 → Fin n := fun g =>
    if h : (g : Set (Fin n)) ∈ 𝓗0 then Fin.castLE (by omega) (col ⟨g.1, h⟩) else fresh
  have hlab : ∀ (g : 𝓗) (h : (g : Set (Fin n)) ∈ 𝓗0), lab g = Fin.castLE (by omega) (col ⟨g.1, h⟩) :=
    fun g h => dif_pos h
  have hlab' : ∀ (g : 𝓗), (g : Set (Fin n)) ∉ 𝓗0 → lab g = fresh := fun g h => dif_neg h
  refine Hypergraph.chromaticIndex_le_of_colorable 𝓗 ⟨⟨lab, ?_⟩⟩
  intro g₁ g₂ hne hnon
  by_cases h1 : (g₁ : Set (Fin n)) ∈ 𝓗0
  · by_cases h2 : (g₂ : Set (Fin n)) ∈ 𝓗0
    · rw [hlab g₁ h1, hlab g₂ h2]
      intro hcontra
      exact hcol ⟨g₁.1, h1⟩ ⟨g₂.1, h2⟩
        (fun h => hne (Subtype.ext (congrArg (fun z : ↥𝓗0 => z.1) h))) hnon
        (Fin.castLE_injective _ hcontra)
    · rw [hlab g₁ h1, hlab' g₂ h2]
      exact hcast _
  · by_cases h2 : (g₂ : Set (Fin n)) ∈ 𝓗0
    · rw [hlab' g₁ h1, hlab g₂ h2]
      exact fun hcontra => hcast _ hcontra.symm
    · rw [hlab' g₁ h1, hlab' g₂ h2]
      intro hcontra
      rcases hnot0 g₁ h1 with hg1 | hg1 <;> rcases hnot0 g₂ h2 with hg2 | hg2
      · exact hne (hg1.trans hg2.symm)
      · rcases hnon with ⟨z, hz1, hz2⟩
        exact (Set.disjoint_left.mp (hisM (Or.inl hg1) (Or.inr hg2) hne)) hz1 hz2
      · rcases hnon with ⟨z, hz1, hz2⟩
        exact (Set.disjoint_left.mp (hisM (Or.inr hg1) (Or.inl hg2) hne)) hz1 hz2
      · rcases hnon with ⟨z, hz1, hz2⟩
        exact (Set.disjoint_left.mp (hisM (Or.inr hg1) (Or.inr hg2) hne)) hz1 hz2


/-! ## The case `U₂ ≠ ∅` -/

/-- The degree of a vertex of `W' ⊆ V^{(n-1)} ∪ V^{(n-2)}` in the induced
2-shadow is at least `|W'| - 3`. -/
theorem ncard_sub_three_le_degIn {𝓗 : Hypergraph (Fin n)} {W W' : Set (Fin n)}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard)
    (hW'sub : W' ⊆ W) (hW : W = Vdeg 𝓗 (n - 1) ∪ Vdeg 𝓗 (n - 2)) (x : ↥W') :
    W'.ncard - 3 ≤ degIn 𝓗.pow2 W' x.1 := by
  classical
  have hxW : x.1 ∈ W := hW'sub x.2
  set N : Set (Fin n) := {y : Fin n | y ∈ W' ∧ ({x.1, y} : Set (Fin n)) ∈ 𝓗.pow2} with hNdef
  have hNsub : N ⊆ W' := fun y hy => hy.1
  have hNdeg : N.ncard = degIn 𝓗.pow2 W' x.1 := by
    rw [degIn_eq_ncard, hNdef]
  have hWN : W'.ncard = (W' \ N).ncard + N.ncard := by
    have hunion : W' = (W' \ N) ∪ N := by
      ext y
      constructor
      · intro hy
        by_cases h : y ∈ N
        · exact Or.inr h
        · exact Or.inl ⟨hy, h⟩
      · rintro (⟨hy, -⟩ | hy)
        · exact hy
        · exact hNsub hy
    have hdisj : Disjoint (W' \ N) N := by
      rw [Set.disjoint_left]
      intro y hy hyN
      exact hy.2 hyN
    conv_lhs => rw [hunion]
    rw [Set.ncard_union_eq hdisj]
  have hnon : {y : Fin n | y ≠ x.1 ∧ ({x.1, y} : Set (Fin n)) ∉ 𝓗}.ncard ≤ 2 := by
    rw [hW] at hxW
    rcases hxW with hx1 | hx2
    · have hempty : {y : Fin n | y ≠ x.1 ∧ ({x.1, y} : Set (Fin n)) ∉ 𝓗} = ∅ := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact fun hyne hy => hy (pairs_of_Vdeg_one hlin hno hx1 y hyne)
      rw [hempty]
      simp
    · exact notAdj_le_two_of_Vdeg_two hlin hno hx2
  have hdiff : (W' \ N).ncard ≤ 3 := by
    have hsub : W' \ N ⊆ ({x.1} : Set (Fin n)) ∪
        {y : Fin n | y ≠ x.1 ∧ ({x.1, y} : Set (Fin n)) ∉ 𝓗} := by
      rintro y ⟨hyW', hyN⟩
      by_cases hyx : y = x.1
      · exact Or.inl (by simpa [hyx])
      · refine Or.inr ⟨hyx, fun hpair => hyN ?_⟩
        rw [hNdef]
        exact ⟨hyW', mem_pow2.mpr ⟨hpair,
          by rw [edgeSize_eq_ncard, Set.ncard_pair (fun h => hyx h.symm)]⟩⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le ({x.1} : Set (Fin n))
      {y : Fin n | y ≠ x.1 ∧ ({x.1, y} : Set (Fin n)) ∉ 𝓗}
    rw [Set.ncard_singleton] at h2
    omega
  rw [← hNdeg]
  omega

/-- **Lemma 7.12, case `U₂ ≠ ∅`.** -/
theorem exists_extension_of_nonempty_U2 {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (hm : DiffMargins n β) (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard)
    (he : e ∈ 𝓗) (he4 : 4 ≤ e.ncard)
    (hU2 : (Vdeg 𝓗 (n - 2)).Nonempty) :
    ∃ M' : Set 𝓗, ({⟨e, he⟩} : Set 𝓗) ⊆ M' ∧ IsMatching 𝓗 M' ∧
      (∀ f ∈ M', f ≠ ⟨e, he⟩ → (f : Set (Fin n)) ∈ 𝓗.pow2) ∧
      Covers M' (Vdeg 𝓗 (n - 1)) ∧
      ((Vdeg 𝓗 (n - 2) \ matchVert M').ncard ≤ 5) := by
  classical
  have hnU : e.ncard ≤ n := by
    have h := Set.ncard_le_ncard (Set.subset_univ e) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨u, huU2⟩ := hU2
  set W : Set (Fin n) := Vdeg 𝓗 (n - 1) ∪ Vdeg 𝓗 (n - 2) with hWdef
  have hU1W : Vdeg 𝓗 (n - 1) ⊆ W := fun x hx => Or.inl hx
  have hU2W : Vdeg 𝓗 (n - 2) ⊆ W := fun x hx => Or.inr hx
  have huW : u ∈ W := hU2W huU2
  have hdisj12 : Disjoint (Vdeg 𝓗 (n - 1)) (Vdeg 𝓗 (n - 2)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Vdeg] at hx1 hx2
    exact absurd (hx1.symm.trans hx2) (by omega)
  have huU1 : u ∉ Vdeg 𝓗 (n - 1) := fun h => (Set.disjoint_left.mp hdisj12) h huU2
  have heW : ∀ v ∈ W, v ∉ e := by
    intro v hv hve
    rcases hv with hv | hv
    · exact (disjoint_e_Vdeg hlin hno he he4 hve).1 hv
    · exact (disjoint_e_Vdeg hlin hno he he4 hve).2 hv
  -- the uniform assembly from a matching `M1`
  have build : ∀ M1 : Set 𝓗, IsMatching 𝓗 M1 → Covers M1 (Vdeg 𝓗 (n - 1)) →
      (∀ f ∈ M1, (f : Set (Fin n)) ⊆ W) → (∀ f ∈ M1, (f : Set (Fin n)) ∈ 𝓗.pow2) →
      ((Vdeg 𝓗 (n - 2) \ matchVert M1).ncard ≤ 5) →
      ∃ M' : Set 𝓗, ({⟨e, he⟩} : Set 𝓗) ⊆ M' ∧ IsMatching 𝓗 M' ∧
        (∀ f ∈ M', f ≠ ⟨e, he⟩ → (f : Set (Fin n)) ∈ 𝓗.pow2) ∧
        Covers M' (Vdeg 𝓗 (n - 1)) ∧
        ((Vdeg 𝓗 (n - 2) \ matchVert M').ncard ≤ 5) := by
    intro M1 hmat hcov hsub hpow hU2b
    have hdisjM : Disjoint (matchVert ({⟨e, he⟩} : Set 𝓗)) (matchVert M1) := by
      rw [Set.disjoint_left]
      intro z hz hzM
      rw [mem_matchVert_singleton] at hz
      rw [mem_matchVert] at hzM
      obtain ⟨g, hg, hzg⟩ := hzM
      exact heW z (hsub g hg hzg) hz
    refine ⟨({⟨e, he⟩} : Set 𝓗) ∪ M1, fun x hx => Or.inl hx, ?_, ?_, ?_, ?_⟩
    · exact isMatching_union (isMatching_singleton 𝓗 ⟨e, he⟩) hmat hdisjM
    · intro f hf hfne
      rw [Set.mem_union] at hf
      rcases hf with hf | hf
      · rw [Set.mem_singleton_iff] at hf
        exact absurd hf hfne
      · exact hpow f hf
    · intro x hx
      rw [matchVert_union]
      exact Or.inr (hcov hx)
    · refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) hU2b
      intro z hz
      exact ⟨hz.1, fun hmem => hz.2 (matchVert_mono (fun y hy => Or.inr hy) hmem)⟩
  rcases Nat.even_or_odd W.ncard with hWev | hWodd
  · -- `|W|` even
    have hWev' : Even (Fintype.card ↥W) := by rw [fintype_card_coe]; exact hWev
    have hdeg : ∀ x : ↥W, Fintype.card ↥W - 3 ≤
        (graphOf 𝓗.pow2 W (fun f hf => (mem_pow2.mp hf).2)).degree x := by
      intro x
      rw [graphOf_degree, fintype_card_coe]
      exact ncard_sub_three_le_degIn (𝓗 := 𝓗) (W := W) (W' := W) hlin hno subset_rfl
        (by rw [hWdef]) x
    rcases Commons.Combinatorics.SimpleGraph.perfectMatching_or_card_le_four
        (graphOf 𝓗.pow2 W (fun f hf => (mem_pow2.mp hf).2)) hWev' hdeg with hperf | hsmall
    obtain ⟨M, hM⟩ := hperf
    · obtain ⟨M1, hmat, hcov, hR, hWsub⟩ := exists_matching_of_perfectMatching
        (𝓗 := 𝓗) (R := 𝓗.pow2) (fun f hf => (mem_pow2.mp hf).1)
        (W := W) (hR2 := fun f hf => (mem_pow2.mp hf).2) hM
      refine build M1 hmat (fun x hx => hcov (hU1W hx))
        (fun f hf z hz => hWsub f hf hz)
        (fun f hf => mem_pow2.mpr ⟨(mem_pow2.mp (hR f hf)).1, (mem_pow2.mp (hR f hf)).2⟩)
        ?_
      have hemp : Vdeg 𝓗 (n - 2) \ matchVert M1 = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzU2, hznot⟩
        exact hznot (hcov (hU2W hzU2))
      rw [hemp]
      simp
    · -- at most four vertices: it suffices to cover `U₁`
      have hWle : W.ncard ≤ 4 := by
        rw [← fintype_card_coe]; exact hsmall
      have hU2le : (Vdeg 𝓗 (n - 2)).ncard ≤ 5 :=
        le_trans (Set.ncard_le_ncard hU2W (Set.toFinite _)) (by omega)
      rcases Nat.even_or_odd (Vdeg 𝓗 (n - 1)).ncard with hev | hodd
      · obtain ⟨M1, hmat, hcov, hsub, hsz⟩ := exists_matching_covering_of_pairs hev
          (fun a ha b hb hab => pairs_of_Vdeg_one hlin hno ha b (fun h => hab h.symm))
        exact build M1 hmat hcov (fun f hf z hz => hU1W (hsub f hf hz))
          (fun f hf => mem_pow2.mpr ⟨f.2, hsz f hf⟩)
          (le_trans (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)) hU2le)
      · obtain ⟨M1, hmat, hcov, hsub, hsz⟩ := exists_matching_covering_of_pairs_odd hodd huU1
          (fun a ha b hb hab => pairs_of_Vdeg_one hlin hno ha b (fun h => hab h.symm))
          (fun a ha => pairs_of_Vdeg_one hlin hno ha u (fun h => huU1 (h ▸ ha)))
        have hWsub1 : ∀ f ∈ M1, (f : Set (Fin n)) ⊆ W := by
          intro f hf z hz
          rcases hsub f hf hz with h | h
          · exact hU1W h
          · rw [show z = u from by simpa using h]; exact huW
        exact build M1 hmat hcov hWsub1 (fun f hf => mem_pow2.mpr ⟨f.2, hsz f hf⟩)
          (le_trans (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)) hU2le)
  · -- `|W|` odd: delete `u`
    have hW'even : Even (Fintype.card ↥(W \ {u})) := by
      rw [fintype_card_coe, Set.ncard_sdiff_singleton_of_mem huW]
      rcases hWodd with ⟨m, hm⟩
      exact ⟨m, by omega⟩
    have hdeg : ∀ x : ↥(W \ {u}), Fintype.card ↥(W \ {u}) - 3 ≤
        (graphOf 𝓗.pow2 (W \ {u}) (fun f hf => (mem_pow2.mp hf).2)).degree x := by
      intro x
      rw [graphOf_degree, fintype_card_coe]
      exact ncard_sub_three_le_degIn (𝓗 := 𝓗) (W := W) (W' := W \ {u}) hlin hno
        Set.sdiff_subset (by rw [hWdef]) x
    rcases Commons.Combinatorics.SimpleGraph.perfectMatching_or_card_le_four
        (graphOf 𝓗.pow2 (W \ {u}) (fun f hf => (mem_pow2.mp hf).2)) hW'even hdeg
      with hperf | hsmall
    obtain ⟨M, hM⟩ := hperf
    · obtain ⟨M1, hmat, hcov, hR, hWsub⟩ := exists_matching_of_perfectMatching
        (𝓗 := 𝓗) (R := 𝓗.pow2) (fun f hf => (mem_pow2.mp hf).1)
        (W := W \ {u}) (hR2 := fun f hf => (mem_pow2.mp hf).2) hM
      refine build M1 hmat (fun x hx => hcov ⟨hU1W hx, fun h => huU1 (h ▸ hx)⟩)
        (fun f hf z hz => (hWsub f hf hz).1)
        (fun f hf => mem_pow2.mpr ⟨(mem_pow2.mp (hR f hf)).1, (mem_pow2.mp (hR f hf)).2⟩)
        ?_
      have hsub2 : Vdeg 𝓗 (n - 2) \ matchVert M1 ⊆ ({u} : Set (Fin n)) := by
        intro z ⟨hzU2, hznot⟩
        by_cases hzu : z = u
        · exact by simp [hzu]
        · exact absurd (hcov ⟨hU2W hzU2, hzu⟩) hznot
      exact le_trans (Set.ncard_le_ncard hsub2 (Set.toFinite _)) (by simp)
    · have hWle : W.ncard ≤ 5 := by
        have h1 : (W \ {u}).ncard + 1 = W.ncard := by
          rw [Set.ncard_sdiff_singleton_of_mem huW]
          have hpos : 0 < W.ncard := by
            rcases hWodd with ⟨m, hm⟩
            omega
          omega
        rw [fintype_card_coe] at hsmall
        omega
      have hU2le : (Vdeg 𝓗 (n - 2)).ncard ≤ 5 :=
        le_trans (Set.ncard_le_ncard hU2W (Set.toFinite _)) hWle
      rcases Nat.even_or_odd (Vdeg 𝓗 (n - 1)).ncard with hev | hodd
      · obtain ⟨M1, hmat, hcov, hsub, hsz⟩ := exists_matching_covering_of_pairs hev
          (fun a ha b hb hab => pairs_of_Vdeg_one hlin hno ha b (fun h => hab h.symm))
        exact build M1 hmat hcov (fun f hf z hz => hU1W (hsub f hf hz))
          (fun f hf => mem_pow2.mpr ⟨f.2, hsz f hf⟩)
          (le_trans (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)) hU2le)
      · obtain ⟨M1, hmat, hcov, hsub, hsz⟩ := exists_matching_covering_of_pairs_odd hodd huU1
          (fun a ha b hb hab => pairs_of_Vdeg_one hlin hno ha b (fun h => hab h.symm))
          (fun a ha => pairs_of_Vdeg_one hlin hno ha u (fun h => huU1 (h ▸ ha)))
        have hWsub1 : ∀ f ∈ M1, (f : Set (Fin n)) ⊆ W := by
          intro f hf z hz
          rcases hsub f hf hz with h | h
          · exact hU1W h
          · rw [show z = u from by simpa using h]; exact huW
        exact build M1 hmat hcov hWsub1 (fun f hf => mem_pow2.mpr ⟨f.2, hsz f hf⟩)
          (le_trans (Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)) hU2le)


/-! ## Lemma 7.12 -/

/-- **Lemma `difficult-edge-absorption`** (Lemma 7.12 of the paper).  If `𝓗` is
a linear hypergraph without singleton edges and `e` is a huge edge, then either
`{e}` extends (using edges of the 2-shadow `G = 𝓗^{(2)}`) to a matching covering
`V^{(n-1)}(𝓗)` and all but at most five vertices of `V^{(n-2)}(𝓗)`, or
`χ'(𝓗) ≤ n`.

(The paper's hypothesis that the matching `{e}` be *difficult* is not used in
the proof, so it is omitted here.) -/
theorem difficult_edge_absorption {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)}
    (hm : DiffMargins n β) (hlin : 𝓗.IsLinear)
    (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) (he : e ∈ 𝓗)
    (hhuge : β * (n : ℝ) / 4 ≤ (e.ncard : ℝ)) :
    (∃ M' : Set 𝓗, ({⟨e, he⟩} : Set 𝓗) ⊆ M' ∧ IsMatching 𝓗 M' ∧
        (∀ f ∈ M', f ≠ ⟨e, he⟩ → (f : Set (Fin n)) ∈ 𝓗.pow2) ∧
        Covers M' (Vdeg 𝓗 (n - 1)) ∧
        ((Vdeg 𝓗 (n - 2) \ matchVert M').ncard ≤ 5)) ∨
      𝓗.chromaticIndex ≤ n := by
  classical
  have he4 : 4 ≤ e.ncard := by
    have h4 : (4 : ℝ) ≤ β * (n : ℝ) / 4 := by
      rw [show β * (n : ℝ) / 4 = (1 / 4) * (β * (n : ℝ)) by ring]
      linarith [hm.hn]
    have : (4 : ℝ) ≤ (e.ncard : ℝ) := le_trans h4 hhuge
    exact_mod_cast this
  rcases Set.eq_empty_or_nonempty (Vdeg 𝓗 (n - 2)) with hU2e | hU2ne
  · rcases Nat.even_or_odd (Vdeg 𝓗 (n - 1)).ncard with hev | hodd
    · exact Or.inl (exists_extension_even hlin hno he he4 hU2e hev)
    · by_cases hX : ∃ y : Fin n, y ∉ e ∧ y ∉ Vdeg 𝓗 (n - 1)
      · obtain ⟨y, hye, hyU⟩ := hX
        exact Or.inl (exists_extension_odd hlin hno he he4 hU2e hodd hyU hye)
      · refine Or.inr (colorable_of_exceptional hlin hno he he4 hU2e hodd ?_)
        intro v
        by_contra hcon
        push Not at hcon
        exact hX ⟨v, hcon.1, hcon.2⟩
  · exact Or.inl (exists_extension_of_nonempty_U2 hm hlin hno he he4 hU2ne)


end

end ErdosFaberLovaszConjecture
