import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- For nonnegative `f`, the sum over a union is at most the sum of the two sums. -/
private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have hun : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [hun, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, f x ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
  linarith

/-- Splitting a window at `11`: for nonnegative summands the reciprocal-prime sum over the
primes of `[A,B]` is at most the sum over the primes of `[A, min B 11]` plus the sum over the
primes of `[11, B]`. -/
theorem primesIn_sum_le_split (A B : ℝ) :
    (∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ))
      ≤ (∑ p ∈ Work.BMF.primesIn A (min B 11), (1 : ℝ) / (p : ℝ))
        + ∑ p ∈ Work.BMF.primesIn 11 B, (1 : ℝ) / (p : ℝ) := by
  have hsub : Work.BMF.primesIn A B ⊆
      Work.BMF.primesIn A (min B 11) ∪ Work.BMF.primesIn 11 B := by
    intro p hp
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨h1, h2⟩, hprime⟩ := hp
    simp only [Finset.mem_union, Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter,
      Finset.mem_Icc]
    rcases lt_or_ge (11 : ℝ) B with hB | hB
    · -- `11 < B`, so `min B 11 = 11` and the two pieces are separated at `p = 11`
      by_cases hp11 : p ≤ 11
      · left
        exact ⟨⟨h1, by rw [min_eq_right hB.le]; simpa using hp11⟩, hprime⟩
      · right
        exact ⟨⟨by simpa using (not_le.mp hp11).le, h2⟩, hprime⟩
    · -- `B ≤ 11`, so `min B 11 = B` and everything lies in the first piece
      left
      exact ⟨⟨h1, by rw [min_eq_left hB]; exact h2⟩, hprime⟩
  calc (∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ))
      ≤ ∑ p ∈ Work.BMF.primesIn A (min B 11) ∪ Work.BMF.primesIn 11 B,
          (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ _ := sum_union_le_of_nonneg _ _ _ (fun p => by positivity)

end Work.BMF.mr_direct
