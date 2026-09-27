import Mathlib
import Submission.Work.Cohomology.EZG.dAux

namespace Work.Cohomology.EZG

/-- Swapping the `insert`ed element (with equal truth values under `P`) does not change the
cardinality of the filtered finset. -/
lemma card_filter_insert_swap {α : Type*} [DecidableEq α] {B : Finset α} {a b : α}
    (P : α → Prop) [DecidablePred P] (ha : a ∉ B) (hb : b ∉ B) (hP : P a ↔ P b) :
    ((insert a B).filter P).card = ((insert b B).filter P).card := by
  rw [Finset.filter_insert, Finset.filter_insert]
  by_cases hpa : P a
  · have hpb : P b := hP.mp hpa
    rw [if_pos hpa, if_pos hpb]
    rw [Finset.card_insert_of_notMem (fun hh => ha (Finset.mem_filter.mp hh).1),
        Finset.card_insert_of_notMem (fun hh => hb (Finset.mem_filter.mp hh).1)]
  · rw [if_neg hpa, if_neg (fun hh => hpa (hP.mpr hh))]

theorem cnt_swapA_of_ne {N : ℕ} (A : Finset (Fin (N+1))) (q : Fin N) (h : q.castSucc ∈ A ↔ q.succ ∉ A) {m : ℕ} (hm : m ≠ (q.succ : ℕ)) : Work.Cohomology.cnt A m = Work.Cohomology.cnt (Work.Cohomology.EZG.swapA N A q) m := by
  have hm' : m ≠ q.val + 1 := by simpa [Fin.val_succ] using hm
  have hiff : ((q.castSucc : Fin (N+1)).val < m) ↔ ((q.succ : Fin (N+1)).val < m) := by
    rw [Fin.val_castSucc, Fin.val_succ]; omega
  unfold Work.Cohomology.cnt
  by_cases hq : q.castSucc ∈ A
  · have hq' : q.succ ∉ A := h.mp hq
    rw [swapA_of_mem hq]
    conv_lhs => rw [show A = insert q.castSucc (A.erase q.castSucc) from (Finset.insert_erase hq).symm]
    exact card_filter_insert_swap (fun i : Fin (N+1) => i.val < m)
      (Finset.notMem_erase _ _) (by rw [Finset.mem_erase]; exact fun hh => hq' hh.2) hiff
  · have hq' : q.succ ∈ A := by by_contra hc; exact hq (h.mpr hc)
    rw [swapA_of_notMem hq]
    conv_lhs => rw [show A = insert q.succ (A.erase q.succ) from (Finset.insert_erase hq').symm]
    exact card_filter_insert_swap (fun i : Fin (N+1) => i.val < m)
      (Finset.notMem_erase _ _) (by rw [Finset.mem_erase]; exact fun hh => hq hh.2) hiff.symm

end Work.Cohomology.EZG
