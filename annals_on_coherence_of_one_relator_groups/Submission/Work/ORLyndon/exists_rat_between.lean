import Mathlib

namespace Work.ORLyndon

theorem exists_rat_between (P N : Finset ℚ) (h : ∀ p ∈ P, ∀ q ∈ N, p < q) :
    ∃ x : ℚ, (∀ p ∈ P, p < x) ∧ (∀ q ∈ N, x < q) := by
  rcases P.eq_empty_or_nonempty with hP | hP
  · -- `P` is empty: any rational below every element of `N` works.
    rcases N.eq_empty_or_nonempty with hN | hN
    · exact ⟨0, by intro p hp; rw [hP] at hp; exact absurd hp (Finset.notMem_empty p),
        by intro q hq; rw [hN] at hq; exact absurd hq (Finset.notMem_empty q)⟩
    · refine ⟨N.min' hN - 1, ?_, ?_⟩
      · intro p hp; rw [hP] at hp; exact absurd hp (Finset.notMem_empty p)
      · intro q hq; have := N.min'_le q hq; linarith
  · rcases N.eq_empty_or_nonempty with hN | hN
    · -- `N` is empty: any rational above every element of `P` works.
      refine ⟨P.max' hP + 1, ?_, ?_⟩
      · intro p hp; have := P.le_max' p hp; linarith
      · intro q hq; rw [hN] at hq; exact absurd hq (Finset.notMem_empty q)
    · -- Both nonempty: the midpoint of `max P` and `min N` works.
      have hlt : P.max' hP < N.min' hN :=
        h (P.max' hP) (P.max'_mem hP) (N.min' hN) (N.min'_mem hN)
      refine ⟨(P.max' hP + N.min' hN) / 2, ?_, ?_⟩
      · intro p hp; have := P.le_max' p hp; linarith
      · intro q hq; have := N.min'_le q hq; linarith

end Work.ORLyndon
