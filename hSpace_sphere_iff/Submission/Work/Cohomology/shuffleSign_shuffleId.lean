import Mathlib
import Submission.Work.Cohomology.EZShuffle

namespace Work.Cohomology

/-- `shuffleId p q = {0, 1, …, p-1}` consists exactly of the indices below `p`. -/
lemma mem_shuffleId {p q : ℕ} {i : Fin (p + q)} : i ∈ shuffleId p q ↔ i.val < p := by
  simp [shuffleId]

/-- No element outside `shuffleId p q` lies below any element of `shuffleId p q`. -/
lemma filter_lt_shuffleId_eq_empty {p q : ℕ} {i : Fin (p + q)} (hi : i ∈ shuffleId p q) :
    (Finset.univ \ shuffleId p q).filter (fun j : Fin (p + q) => j.val < i.val) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
  exact hj.1 ((mem_shuffleId (p := p) (q := q)).mpr (lt_trans hj.2 ((mem_shuffleId).mp hi)))

/-- The sign of the trivial `(p,q)`-shuffle is `1`. -/
theorem shuffleSign_shuffleId (p q : ℕ) : Work.Cohomology.shuffleSign (Work.Cohomology.shuffleId p q) = 1 := by
  unfold Work.Cohomology.shuffleSign
  have h : ((Work.Cohomology.shuffleId p q).sum fun i =>
      ((Finset.univ \ Work.Cohomology.shuffleId p q).filter
        fun j : Fin (p + q) => j.val < i.val).card) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [filter_lt_shuffleId_eq_empty hi, Finset.card_empty]
  rw [h]
  norm_num

end Work.Cohomology
