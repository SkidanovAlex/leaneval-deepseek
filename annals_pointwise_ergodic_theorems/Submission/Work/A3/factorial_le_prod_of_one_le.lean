import Mathlib

namespace Work.A3

/-- For a finset of positive naturals, the product of its elements is at least the factorial
of its cardinality: the smallest possible product of `n` distinct positive integers is `n!`. -/
theorem factorial_le_prod_of_one_le (s : Finset ℕ) (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  revert hs
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    simp
  · intro a t hlt ih hs
    have ha : 1 ≤ a := hs a (Finset.mem_insert_self a t)
    have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hanot : a ∉ t := fun h => absurd (hlt a h) (lt_irrefl a)
    -- every element of `t` lies in `{1, …, a-1}`, so `t` has at most `a - 1` elements
    have hcard : t.card + 1 ≤ a := by
      have hsub : t ⊆ Finset.Icc 1 (a - 1) := by
        intro x hx
        simp only [Finset.mem_Icc]
        exact ⟨ht x hx, by have := hlt x hx; omega⟩
      have := Finset.card_le_card hsub
      simp only [Nat.card_Icc] at this
      omega
    rw [Finset.card_insert_of_notMem hanot, Finset.prod_insert hanot, Nat.factorial_succ]
    exact Nat.mul_le_mul hcard (ih ht)

end Work.A3
