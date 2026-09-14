import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Commons.Algebra.BigOperators

theorem prod_filter_lt_split (s : Finset ℕ) {n Y : ℕ} (hnY : n < Y) :
    (∏ p ∈ s.filter (fun p => p < Y), p) =
      (∏ p ∈ s.filter (fun p => n < p ∧ p < Y), p) *
        (∏ p ∈ s.filter (fun p => p ≤ n), p) := by
  have hdisj :
      Disjoint (s.filter (fun p => n < p ∧ p < Y)) (s.filter (fun p => p ≤ n)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter] at hp hq
    omega
  have hA : s.filter (fun p => p < Y) =
      s.filter (fun p => n < p ∧ p < Y) ∪ s.filter (fun p => p ≤ n) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp, hY⟩
      rcases lt_or_ge n p with h | h
      · exact Or.inl ⟨hp, h, hY⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, h, hY⟩ | ⟨hp, h⟩)
      · exact ⟨hp, hY⟩
      · exact ⟨hp, lt_of_le_of_lt h hnY⟩
  rw [hA, Finset.prod_union hdisj]

end Commons.Algebra.BigOperators