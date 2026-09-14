import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Abel

namespace Commons.Analysis.Sum

/-- A double sum over the off-diagonal pairs of a finset equals the nested sum with
`s.erase i` as the inner index set. -/
lemma sum_offDiag_eq {α M : Type*} [DecidableEq α] [AddCommGroup M] (s : Finset α)
    (f : α × α → M) :
    ∑ p ∈ s.offDiag, f p = ∑ i ∈ s, ∑ j ∈ s.erase i, f (i, j) := by
  have hP : (∑ p ∈ s ×ˢ s, f p) = ∑ i ∈ s, ∑ j ∈ s, f (i, j) := Finset.sum_product s s f
  have hD : (∑ p ∈ s.diag, f p) = ∑ i ∈ s, f (i, i) := Finset.sum_diag s f
  have hU : (∑ p ∈ s ×ˢ s, f p) = (∑ p ∈ s.diag, f p) + ∑ p ∈ s.offDiag, f p := by
    rw [← Finset.diag_union_offDiag s, Finset.sum_union (Finset.disjoint_diag_offDiag s)]
  have hoff : (∑ p ∈ s.offDiag, f p) = (∑ p ∈ s ×ˢ s, f p) - ∑ p ∈ s.diag, f p := by
    rw [hU]; abel
  rw [hoff, hP, hD, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_erase_eq_sub hi]

theorem antisymm_double_sum_zero {α M : Type*} [DecidableEq α] [AddCommGroup M] (s : Finset α)
    (F : α → α → M) (hanti : ∀ i j, F i j = - F j i) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, F i j = 0 := by
  rw [← sum_offDiag_eq s (fun p => F p.1 p.2)]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    show F p.1 p.2 + F p.2 p.1 = 0
    rw [hanti p.1 p.2]
    exact neg_add_cancel _
  · intro p hp hf hg
    exact absurd (Prod.ext_iff.mp hg).2 (Finset.mem_offDiag.1 hp).2.2
  · intro p hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.1 hp
    exact Finset.mem_offDiag.2 ⟨h2, h1, fun h => hne h.symm⟩
  · intro p hp
    exact Prod.mk.eta

end Commons.Analysis.Sum