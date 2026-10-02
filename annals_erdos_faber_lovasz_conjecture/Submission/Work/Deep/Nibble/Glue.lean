import Submission.Work.Deep.Nibble.Defs

/-!
# The API of the chapter's vocabulary

Basic lemmas about the notions introduced in `Work.Deep.Nibble.Defs`
(`MultiHypergraph.edgeSet`, `MultiHypergraph.IsMatching`, `EdgeDisjointFam`,
`famVert`, `CoversFamMulti`, `PseudoRandomFam`, `LeftoverFam`,
`NearlyPerfectCoverageFam`, `EdgePartition`) together with the bridges that
identify them with the analogous cone notions (`matchVert`, `Covers`,
`PseudoRandom`, `PerfectCoverage`, `NearlyPerfectCoverage` of
`Submission/EFL/{Reservoir,Absorption}.lean`), so that a consumer can move
freely between the two languages.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

namespace MultiHypergraph

theorem mem_edges_of_edgeSet_of_not_singleton {𝓜 : MultiHypergraph n} {e : Set (Fin n)}
    (he : e ∈ 𝓜.edgeSet) (hnot : ¬ ∃ v : Fin n, e = {v}) : e ∈ 𝓜.edges :=
  he.resolve_right (fun h => hnot ⟨h.choose, h.choose_spec.1⟩)

/-- `edgeSet` is monotone. -/
theorem edgeSet_mono {𝓜 𝓝 : MultiHypergraph n} (h : 𝓜 ≤ 𝓝) : 𝓜.edgeSet ⊆ 𝓝.edgeSet := by
  intro e he
  rcases he with he | ⟨v, rfl, hv⟩
  · exact Or.inl (h.1 he)
  · refine Or.inr ⟨v, rfl, ?_⟩
    have := h.2 v
    omega

/-- Matchings are preserved by shrinking the family. -/
theorem isMatching_mono {𝓜 : MultiHypergraph n} {N N' : Set (Set (Fin n))}
    (h : N ⊆ N') (hN : 𝓜.IsMatching N') : 𝓜.IsMatching N :=
  ⟨fun e he => hN.1 (h he), hN.2.mono h⟩

/-- The empty family is a matching. -/
theorem isMatching_empty (𝓜 : MultiHypergraph n) : 𝓜.IsMatching (∅ : Set (Set (Fin n))) :=
  ⟨by simp, by simp⟩

/-- A subfamily of a matching is a matching. -/
theorem IsMatching.subset {𝓜 : MultiHypergraph n} {N N' : Set (Set (Fin n))}
    (hN : 𝓜.IsMatching N) (h : N' ⊆ N) : 𝓜.IsMatching N' :=
  isMatching_mono h hN

end MultiHypergraph

/-! ## `EdgeDisjointFam`, `famVert`, `CoversFamMulti` -/

theorem edgeDisjointFam_comm {N N' : Set (Set (Fin n))} (h : EdgeDisjointFam N N') :
    EdgeDisjointFam N' N := h.symm

theorem edgeDisjointFam_mono {N₁ N₂ N₁' N₂' : Set (Set (Fin n))}
    (h₁ : N₁ ⊆ N₁') (h₂ : N₂ ⊆ N₂') (h : EdgeDisjointFam N₁' N₂') :
    EdgeDisjointFam N₁ N₂ := by
  rw [EdgeDisjointFam, Set.disjoint_left] at h ⊢
  intro e he he'
  exact h ⟨h₁ he.1, he.2⟩ ⟨h₂ he'.1, he'.2⟩

theorem famVert_mono {N N' : Set (Set (Fin n))} (h : N ⊆ N') : famVert N ⊆ famVert N' := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_famVert.mp hv
  exact mem_famVert.mpr ⟨e, h he, hve⟩

theorem famVert_union (N N' : Set (Set (Fin n))) : famVert (N ∪ N') = famVert N ∪ famVert N' := by
  ext v
  rw [mem_famVert, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hve⟩
    · exact Or.inl ⟨e, he, hve⟩
    · exact Or.inr ⟨e, he, hve⟩
  · rintro (⟨e, he, hve⟩ | ⟨e, he, hve⟩)
    · exact ⟨e, Or.inl he, hve⟩
    · exact ⟨e, Or.inr he, hve⟩

theorem famVert_subset_self {N : Set (Set (Fin n))} : ∀ e ∈ N, e ⊆ famVert N :=
  fun e he v hv => mem_famVert.mpr ⟨e, he, hv⟩

theorem coversFamMulti_mono {N N' : Set (Set (Fin n))} {X Y : Set (Fin n)}
    (hNN' : N ⊆ N') (hYX : Y ⊆ X) (h : CoversFamMulti N X) : CoversFamMulti N' Y :=
  fun v hv => famVert_mono hNN' (h (hYX hv))

/-- If `X ⊆ Y` and `Y` is covered, so is `X`. -/
theorem CoversFamMulti.mono {N : Set (Set (Fin n))} {X Y : Set (Fin n)}
    (hXY : X ⊆ Y) (h : CoversFamMulti N Y) : CoversFamMulti N X :=
  fun v hv => h (hXY hv)

/-! ## `LeftoverFam` and `PseudoRandomFam` API -/

theorem LeftoverFam.mono {D : ℕ} {N : Fin D → Set (Set (Fin n))}
    {𝓕E 𝓕E' : Set (Set (Set (Fin n)))} {γ κ : ℝ} (h : 𝓕E ⊆ 𝓕E')
    (hL : LeftoverFam N 𝓕E' γ κ) : LeftoverFam N 𝓕E γ κ :=
  fun _F hF => hL _F (h hF)

theorem PseudoRandomFam.mono {N : Set (Set (Fin n))} {𝓕V 𝓕V' : Set (Set (Fin n))}
    {γ κ : ℝ} (h : 𝓕V ⊆ 𝓕V') (hP : PseudoRandomFam N 𝓕V' γ κ) :
    PseudoRandomFam N 𝓕V γ κ :=
  fun _A hA => hP _A (h hA)

/-! ## Bridges to the cone's `matchVert` / `Covers` / `PseudoRandom` -/

theorem pseudoRandom_famOf_iff {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗)
    (𝓕 : Set (Set (Fin n))) (γ κ : ℝ) :
    PseudoRandom M 𝓕 γ κ ↔ PseudoRandomFam (famOf M) 𝓕 γ κ := by
  constructor <;> intro h S hS <;>
    simpa only [PseudoRandom, PseudoRandomFam, famVert_famOf] using h S hS

theorem perfectCoverage_famOf_iff {ι : Type*} {𝓗 : Hypergraph (Fin n)}
    (N : ι → Set 𝓗) (U : Set (Fin n)) :
    PerfectCoverage N U ↔ ∀ i, CoversFamMulti (famOf (N i)) U := by
  simp only [PerfectCoverage, coversFamMulti_famOf]

theorem nearlyPerfectCoverage_famOf_iff {ι : Type*} [Fintype ι]
    {𝓗 : Hypergraph (Fin n)} (N : ι → Set 𝓗) (U S : Set (Fin n)) :
    NearlyPerfectCoverage N U S ↔ NearlyPerfectCoverageFam (fun i => famOf (N i)) U S := by
  simp only [NearlyPerfectCoverage, NearlyPerfectCoverageFam, famVert_famOf]

end

end ErdosFaberLovaszConjecture
