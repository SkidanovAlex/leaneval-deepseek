import Mathlib
import Submission.Work.LT.good_base_defs

/-!
# Hamming norm of a matrix and agreement bounds

Elementary lemmas about `hammingNorm` on a product type, used in the proof of the
Kalachev--Panteleev "zero rectangle" Lemma 10 (`Work.LT.gb_zero_rect_of_star`):

* the Hamming norm of `x : α × β → γ` is the sum of the Hamming norms of its rows (resp. columns);
* if `f` and `g` agree on a set `A`, the support of `f` is contained in the support of `g`
  together with the complement of `A`.
-/

namespace Work.LT

/-- The Hamming norm of a function on a product is the sum over the first coordinate of the
Hamming norms of the "rows" `b ↦ x (a, b)`. -/
lemma hammingNorm_prod_eq_sum {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ] [Zero γ]
    (x : α × β → γ) : hammingNorm x = ∑ a, hammingNorm (fun b => x (a, b)) := by
  simp only [hammingNorm]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The Hamming norm of a function on a product is the sum over the second coordinate of the
Hamming norms of the "columns" `a ↦ x (a, b)`. -/
lemma hammingNorm_prod_eq_sum_col {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ] [Zero γ]
    (x : α × β → γ) : hammingNorm x = ∑ b, hammingNorm (fun a => x (a, b)) := by
  simp only [hammingNorm]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- If `f` and `g` agree on the set `A`, then the support of `f` is contained in the support of
`g` together with the complement of `A`; in particular `hammingNorm f ≤ hammingNorm g + |Aᶜ|`. -/
lemma hammingNorm_le_add_sdiff {ι γ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq γ] [Zero γ]
    (f g : ι → γ) (A : Finset ι) (h : ∀ i ∈ A, f i = g i) :
    hammingNorm f ≤ hammingNorm g + (Finset.univ \ A).card := by
  rw [hammingNorm, hammingNorm]
  calc (Finset.univ.filter (fun i => f i ≠ 0)).card
      ≤ ((Finset.univ.filter (fun i => g i ≠ 0)) ∪ (Finset.univ \ A)).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_union]
        by_cases hA : i ∈ A
        · left; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, by rw [← h i hA]; exact hi.2⟩
        · right; rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ i, hA⟩
    _ ≤ (Finset.univ.filter (fun i => g i ≠ 0)).card + (Finset.univ \ A).card :=
        Finset.card_union_le _ _

end Work.LT
