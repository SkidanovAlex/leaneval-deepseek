import Mathlib.Data.Set.Finite.Lattice

namespace Commons.Set.Infinite

theorem infinite_of_finite_cover {α : Type*} {S : Set α} (hS : S.Infinite)
    {ι : Type*} [Fintype ι] (A : ι → Set α) (hcover : S ⊆ ⋃ i, A i) :
    ∃ i, (S ∩ A i).Infinite := by
  by_contra h
  rw [not_exists] at h
  have hfin : ∀ i, (S ∩ A i).Finite := fun i => by
    by_contra hc
    exact h i hc
  have hsub : S ⊆ ⋃ i, (S ∩ A i) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  have hfin' : (⋃ i, (S ∩ A i)).Finite := Set.finite_iUnion hfin
  exact hS (hfin'.subset hsub)

end Commons.Set.Infinite