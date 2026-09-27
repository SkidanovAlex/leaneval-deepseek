import Mathlib

namespace Work.EKLC6Core

theorem dense_disjoint_iff {α : Type*} [TopologicalSpace α] {U O O₂ : Set α} (hO : IsOpen O)
    (hsub : O₂ ⊆ U) {D : Set α} (hDsub : D ⊆ O₂)
    (hDense : ∀ O' : Set α, IsOpen O' → (O' ∩ O₂).Nonempty → (O' ∩ D).Nonempty) :
    (O ∩ U) ∩ O₂ = ∅ ↔ ∀ d ∈ D, d ∉ O ∩ U := by
  constructor
  · -- If the intersection is empty, no point of `D` (⊆ O₂) lies in `O ∩ U`.
    intro h d hd hdO
    have hdO₂ : d ∈ O₂ := hDsub hd
    have hmem : d ∈ (O ∩ U) ∩ O₂ := ⟨hdO, hdO₂⟩
    rw [h] at hmem
    exact hmem
  · -- Conversely, density of `D` in `O₂` forces a witness in `O ∩ U` whenever
    -- a point of `O ∩ O₂` exists, and `O` is open.
    intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxOU, hxO₂⟩ := hx
    rw [Set.mem_inter_iff] at hxOU
    obtain ⟨hxO, _⟩ := hxOU
    have hne : (O ∩ O₂).Nonempty := ⟨x, hxO, hxO₂⟩
    obtain ⟨d, hdO, hdD⟩ := hDense O hO hne
    have hdU : d ∈ U := hsub (hDsub hdD)
    exact h d hdD ⟨hdO, hdU⟩

end Work.EKLC6Core
