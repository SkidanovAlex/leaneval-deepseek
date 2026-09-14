import Mathlib.Data.Set.Finite.Lattice

namespace Commons.Combinatorics

theorem infinite_fiber {α β : Type*} [Finite β] {s : Set α} (hs : s.Infinite)
    (f : α → β) : ∃ b : β, (s ∩ f ⁻¹' {b}).Infinite := by
  by_contra h
  simp only [not_exists, Set.not_infinite] at h
  have hfin : (⋃ b, (s ∩ f ⁻¹' {b}) : Set α).Finite :=
    Set.finite_iUnion (fun b => h b)
  have hsub : s ⊆ ⋃ b, (s ∩ f ⁻¹' {b}) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨f x, hx, rfl⟩
  exact hs (hfin.subset hsub)

end Commons.Combinatorics