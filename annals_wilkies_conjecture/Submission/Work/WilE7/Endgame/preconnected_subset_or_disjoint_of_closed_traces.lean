import Mathlib

namespace Work.WilE7.Endgame

/-- Auxiliary: if each `T i` is either contained in `A` or disjoint from `A`, and `T i`
agrees with a closed set `F i` on `K`, then the part of a preconnected `κ ⊆ K` covered by the
`A`-side and the part covered by the complement side cannot both be nonempty (this would give a
nonempty intersection of the two closed pieces). -/
theorem preconnected_subset_or_disjoint_of_closed_traces {X : Type*} [TopologicalSpace X]
    {K A κ : Set X} {ι : Type*} [Finite ι] (F T : ι → Set X)
    (hκ : IsPreconnected κ) (hκK : κ ⊆ K)
    (hF : ∀ i, IsClosed (F i)) (htr : ∀ i, F i ∩ K = T i ∩ K)
    (hcover : κ ⊆ ⋃ i, T i)
    (hor : ∀ i, T i ⊆ A ∨ Disjoint (T i) A) :
    κ ⊆ A ∨ Disjoint κ A := by
  classical
  -- The closed set collecting the `F i` that lie on the `A`-side...
  set C : Set X := ⋃ i ∈ {i | T i ⊆ A}, F i with hC
  -- ... and the closed set collecting the `F i` that are disjoint from `A`.
  set D : Set X := ⋃ i ∈ {i | Disjoint (T i) A}, F i with hD
  have hfin : ({i : ι | T i ⊆ A} : Set ι).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hfin' : ({i : ι | Disjoint (T i) A} : Set ι).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hCclosed : IsClosed C := by
    rw [hC]
    exact Set.Finite.isClosed_biUnion hfin (fun i _ => hF i)
  have hDclosed : IsClosed D := by
    rw [hD]
    exact Set.Finite.isClosed_biUnion hfin' (fun i _ => hF i)
  -- `κ` is covered by `C ∪ D`.
  have hsub : κ ⊆ C ∪ D := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    have hxFi : x ∈ F i := by
      have : x ∈ F i ∩ K := by rw [htr i]; exact ⟨hxi, hκK hx⟩
      exact this.1
    rcases hor i with hle | hdisj
    · left
      rw [hC]
      exact Set.mem_iUnion₂.mpr ⟨i, hle, hxFi⟩
    · right
      rw [hD]
      exact Set.mem_iUnion₂.mpr ⟨i, hdisj, hxFi⟩
  -- On `κ`, the piece `C` lies inside `A`.
  have hCA : κ ∩ C ⊆ A := by
    rintro x ⟨hxκ, hxC⟩
    rw [hC] at hxC
    rcases Set.mem_iUnion₂.mp hxC with ⟨i, hi, hxFi⟩
    have : x ∈ F i ∩ K := ⟨hxFi, hκK hxκ⟩
    rw [htr i] at this
    exact hi this.1
  -- On `κ`, the piece `D` is disjoint from `A`.
  have hDA : Disjoint (κ ∩ D) A := by
    rw [Set.disjoint_left]
    rintro x ⟨hxκ, hxD⟩ hxA
    rw [hD] at hxD
    rcases Set.mem_iUnion₂.mp hxD with ⟨i, hi, hxFi⟩
    have : x ∈ F i ∩ K := ⟨hxFi, hκK hxκ⟩
    rw [htr i] at this
    exact (Set.disjoint_left.mp hi) this.1 hxA
  -- Preconnectedness: if both `κ ∩ C` and `κ ∩ D` were nonempty, they would meet, which is
  -- impossible since one is contained in `A` and the other is disjoint from `A`.
  have key := (isPreconnected_closed_iff.mp hκ) C D hCclosed hDclosed hsub
  by_cases hCne : (κ ∩ C).Nonempty
  · by_cases hDne : (κ ∩ D).Nonempty
    · exfalso
      obtain ⟨x, hxκ, hxC, hxD⟩ := key hCne hDne
      have hxA : x ∈ A := hCA ⟨hxκ, hxC⟩
      exact (Set.disjoint_left.mp hDA) ⟨hxκ, hxD⟩ hxA
    · left
      intro x hxκ
      rcases hsub hxκ with hxC | hxD
      · exact hCA ⟨hxκ, hxC⟩
      · exact absurd ⟨x, hxκ, hxD⟩ hDne
  · right
    rw [Set.disjoint_left]
    intro x hxκ hxA
    rcases hsub hxκ with hxC | hxD
    · exact hCne ⟨x, hxκ, hxC⟩
    · exact (Set.disjoint_left.mp hDA) ⟨hxκ, hxD⟩ hxA

end Work.WilE7.Endgame
