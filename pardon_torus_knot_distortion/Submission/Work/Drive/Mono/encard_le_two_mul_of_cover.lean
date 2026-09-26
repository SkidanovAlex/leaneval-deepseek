import Mathlib

open Set

namespace Work.Drive.Mono

/-- The frontier of a finite union of closed intervals `⋃ i, Icc (a i) (b i)` is contained in the
(finite) set of the `2 * m` endpoints `range a ∪ range b`.  Hence any `S` contained in that frontier
has extended cardinality at most `2 * m`. -/
theorem encard_le_two_mul_of_cover {S : Set ℝ} {m : ℕ} (a b : Fin m → ℝ)
    (hS : S ⊆ frontier (⋃ i : Fin m, Set.Icc (a i) (b i))) : Set.encard S ≤ 2 * m := by
  -- A point of the frontier which is not an endpoint already lies in the interior.
  have hsub : S ⊆ Set.range a ∪ Set.range b := by
    intro x hx
    have hxf := hS hx
    have hclosed : IsClosed (⋃ i : Fin m, Set.Icc (a i) (b i)) :=
      isClosed_iUnion_of_finite (fun i => isClosed_Icc)
    have hxU : x ∈ (⋃ i : Fin m, Set.Icc (a i) (b i)) :=
      IsClosed.frontier_subset hclosed hxf
    have hxni : x ∉ interior (⋃ i : Fin m, Set.Icc (a i) (b i)) :=
      (mem_frontier_iff_notMem_interior hxU).mp hxf
    rw [mem_iUnion] at hxU
    obtain ⟨i, hi⟩ := hxU
    have h1 : a i ≤ x := hi.1
    have h2 : x ≤ b i := hi.2
    rcases eq_or_lt_of_le h1 with h | h
    · exact Or.inl ⟨i, h⟩
    · rcases eq_or_lt_of_le h2 with h' | h'
      · exact Or.inr ⟨i, h'.symm⟩
      · exfalso
        exact hxni (interior_mono (Set.subset_iUnion _ i)
          (by rw [interior_Icc]; exact ⟨h, h'⟩))
  -- Each of the two ranges has at most `m` elements.
  have hra : (Set.range a).encard ≤ (m : ℕ∞) := by
    rw [← Set.image_univ]
    exact (Set.encard_image_le a Set.univ).trans (by simp)
  have hrb : (Set.range b).encard ≤ (m : ℕ∞) := by
    rw [← Set.image_univ]
    exact (Set.encard_image_le b Set.univ).trans (by simp)
  calc Set.encard S ≤ (Set.range a ∪ Set.range b).encard := Set.encard_le_encard hsub
    _ ≤ (Set.range a).encard + (Set.range b).encard := Set.encard_union_le _ _
    _ ≤ (m : ℕ∞) + m := add_le_add hra hrb
    _ = 2 * m := by rw [two_mul]

end Work.Drive.Mono
