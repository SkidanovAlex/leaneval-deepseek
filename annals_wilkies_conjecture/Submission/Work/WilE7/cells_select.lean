import Mathlib
import Submission.Work.WilE7.Defs

namespace Work.WilE7

/-- Selection lemma for finite lists of `*`-pieces.

If every piece of `K` is compatible (contained in or disjoint from) with every `κ ∈ C`, every
piece of `L` outside `K` is either empty or the whole cube, and every `κ ∈ C` sits inside the
cube, then the union of all pieces of `L` is compatible with every `κ ∈ C`.

The hypothesis that `K` is a sub-list of `L` is not needed for this combinatorial statement;
it is kept in `cells_select` because that is where the mathematics supplies it. -/
theorem union_list_compatible {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    {L K : List (WilkiesDesign.E.StarPiece n)}
    (hC : ∀ κ ∈ C, κ ⊆ WilkiesDesign.E.cubeC n)
    (hLK : ∀ P ∈ L, P ∉ K → P.set = ∅ ∨ P.set = WilkiesDesign.E.cubeC n)
    (hK : ∀ P ∈ K, ∀ κ ∈ C, κ ⊆ P.set ∨ Disjoint κ P.set) :
    ∀ κ ∈ C, κ ⊆ (⋃ P ∈ L, P.set) ∨ Disjoint κ (⋃ P ∈ L, P.set) := by
  intro κ hκ
  have key : ∀ P ∈ L, κ ⊆ P.set ∨ Disjoint κ P.set := by
    intro P hPL
    by_cases hPK : P ∈ K
    · exact hK P hPK κ hκ
    · rcases hLK P hPL hPK with h0 | hc
      · right; rw [h0]; exact disjoint_bot_right
      · left; rw [hc]; exact hC κ hκ
  by_cases h : ∃ P, P ∈ L ∧ κ ⊆ P.set
  · left
    obtain ⟨P, hPL, hsub⟩ := h
    intro x hx
    exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hPL, hsub hx⟩⟩
  · right
    rw [Set.disjoint_left]
    intro x hxκ hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨P, hxU⟩ := hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨hPL, hxP⟩ := hxU
    rcases key P hPL with hsub | hdj
    · exact h ⟨P, hPL, hsub⟩
    · exact (Set.disjoint_left.mp hdj hxκ) hxP

theorem cells_select :
    (∀ {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {Y : Set (Fin n → ℝ)},
        (∀ κ ∈ C, κ ⊆ WilkiesDesign.E.cubeC n) →
        WilkiesDesign.E.cubeC n ⊆ ⋃₀ (C : Set (Set (Fin n → ℝ))) →
        (∀ κ ∈ C, κ ⊆ Y ∨ Disjoint κ Y) →
        ⋃₀ (Work.WilE7.cellsOutside C Y : Set (Set (Fin n → ℝ))) =
          WilkiesDesign.E.cubeC n \ Y) ∧
    (∀ {n k : ℕ} {C : Finset (Set (Fin n → ℝ))} (Y : Fin k → Set (Fin n → ℝ)),
        (∀ κ ∈ C, κ ⊆ WilkiesDesign.E.cubeC n) →
        WilkiesDesign.E.cubeC n ⊆ ⋃₀ (C : Set (Set (Fin n → ℝ))) →
        (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) →
        ⋃₀ (Work.WilE7.cellsInside C Y : Set (Set (Fin n → ℝ))) =
          WilkiesDesign.E.cubeC n ∩ ⋂ i, Y i) ∧
    (∀ {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {L K : List (WilkiesDesign.E.StarPiece n)},
        (∀ κ ∈ C, κ ⊆ WilkiesDesign.E.cubeC n) →
        (∀ P ∈ K, P ∈ L) →
        (∀ P ∈ L, P ∉ K → P.set = ∅ ∨ P.set = WilkiesDesign.E.cubeC n) →
        (∀ P ∈ K, ∀ κ ∈ C, κ ⊆ P.set ∨ Disjoint κ P.set) →
        ∀ κ ∈ C, κ ⊆ (⋃ P ∈ L, P.set) ∨ Disjoint κ (⋃ P ∈ L, P.set)) ∧
    (∀ {n k : ℕ} {C : Finset (Set (Fin n → ℝ))} (L K : Fin k → List (WilkiesDesign.E.StarPiece n)),
        (∀ κ ∈ C, κ ⊆ WilkiesDesign.E.cubeC n) →
        (∀ i, ∀ P ∈ K i, P ∈ L i) →
        (∀ i, ∀ P ∈ L i, P ∉ K i → P.set = ∅ ∨ P.set = WilkiesDesign.E.cubeC n) →
        (∀ i, ∀ P ∈ K i, ∀ κ ∈ C, κ ⊆ P.set ∨ Disjoint κ P.set) →
        ∀ i, ∀ κ ∈ C, κ ⊆ (⋃ P ∈ L i, P.set) ∨ Disjoint κ (⋃ P ∈ L i, P.set)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n C Y hsub hcover hcompat
    ext x
    simp only [Set.mem_sUnion, Set.mem_sdiff, Finset.mem_filter, Finset.mem_coe, cellsOutside]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨hsC, hsdj⟩ := hs
      exact ⟨hsub s hsC hxs, fun hxY => (Set.disjoint_left.mp hsdj hxs) hxY⟩
    · rintro ⟨hxcube, hxY⟩
      have hxU : x ∈ ⋃₀ (C : Set (Set (Fin n → ℝ))) := hcover hxcube
      rw [Set.mem_sUnion] at hxU
      obtain ⟨s, hsC, hxs⟩ := hxU
      rcases hcompat s hsC with hsub' | hdj
      · exact absurd (hsub' hxs) hxY
      · exact ⟨s, ⟨hsC, hdj⟩, hxs⟩
  · intro n k C Y hsub hcover hcompat
    ext x
    simp only [Set.mem_sUnion, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_filter, Finset.mem_coe,
      cellsInside]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨hsC, hsubY⟩ := hs
      exact ⟨hsub s hsC hxs, fun i => hsubY i hxs⟩
    · rintro ⟨hxcube, hxY⟩
      have hxU : x ∈ ⋃₀ (C : Set (Set (Fin n → ℝ))) := hcover hxcube
      rw [Set.mem_sUnion] at hxU
      obtain ⟨s, hsC, hxs⟩ := hxU
      refine ⟨s, ⟨hsC, fun i => ?_⟩, hxs⟩
      rcases hcompat i s hsC with hsub' | hdj
      · exact hsub'
      · exact absurd (hxY i) (Set.disjoint_left.mp hdj hxs)
  · intro n C L K hC _hKL hLK hK
    exact union_list_compatible hC hLK hK
  · intro n k C L K hC _hKL hLK hK i
    exact union_list_compatible hC (hLK i) (hK i)

end Work.WilE7
