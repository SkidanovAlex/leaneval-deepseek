import Mathlib

namespace Work.ANALYTIC.CechPt

/-- Gluing lemma for the Cech-level linear-independence construction: if `(B i)` is a directed
family of linearly independent sets whose spans are `N ⊓ ℤ[Y i]`, then the union is linearly
independent and spans `N ⊓ ℤ[⋃ i, Y i]`. -/
theorem linearIndepOn_iUnion_span {X : Type*} {ι : Type*} (N : Submodule ℤ (X →₀ ℤ))
    (Y : ι → Set X) (B : ι → Set (X →₀ ℤ)) (hY : Directed (· ⊆ ·) Y) (hB : Directed (· ⊆ ·) B)
    (hli : ∀ i, LinearIndepOn ℤ id (B i))
    (hsp : ∀ i, Submodule.span ℤ (B i) = N ⊓ Finsupp.supported ℤ ℤ (Y i)) :
    LinearIndepOn ℤ id (⋃ i, B i) ∧
      Submodule.span ℤ (⋃ i, B i) = N ⊓ Finsupp.supported ℤ ℤ (⋃ i, Y i) := by
  classical
  constructor
  · exact linearIndepOn_iUnion_of_directed hB hli
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      have h1 : x ∈ Submodule.span ℤ (B i) := Submodule.subset_span hxi
      rw [hsp i, Submodule.mem_inf] at h1
      exact ⟨h1.1, Finsupp.supported_mono (Set.subset_iUnion Y i) h1.2⟩
    · rintro x hx
      rw [Submodule.mem_inf, Finsupp.mem_supported] at hx
      obtain ⟨hxN, hxS⟩ := hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · -- `x` has nonempty finite support, so some index exists; use it to run `finset_le`
        have hne : Nonempty ι := by
          obtain ⟨a₀, ha₀⟩ := Finsupp.support_nonempty_iff.mpr hx0
          obtain ⟨i₀, -⟩ := Set.mem_iUnion.mp (hxS ha₀)
          exact ⟨i₀⟩
        have := hne
        choose g hg using fun a : x.support => Set.mem_iUnion.mp (hxS a.2)
        obtain ⟨k, hk⟩ := hY.finset_le (Finset.univ.image g)
        have hbased : (x.support : Set X) ⊆ Y k := by
          intro a ha
          exact hk (g ⟨a, ha⟩)
            (Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩) (hg ⟨a, ha⟩)
        have hxk : x ∈ Submodule.span ℤ (B k) := by
          rw [hsp k, Submodule.mem_inf]
          exact ⟨hxN, (Finsupp.mem_supported ℤ x).mpr hbased⟩
        exact Submodule.span_mono (Set.subset_iUnion B k) hxk

end Work.ANALYTIC.CechPt
