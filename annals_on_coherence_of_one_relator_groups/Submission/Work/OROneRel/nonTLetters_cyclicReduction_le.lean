import Mathlib
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate

namespace Work.OROneRel

open FreeGroup

/-- `FreeGroup.reduceCyclically L` is a sublist of `L`: it is obtained by cancelling matching
pairs of letters from the two ends.  This follows from Mathlib's
`FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically`, which exhibits
`reduceCyclically L` as an infix word of `L`. -/
theorem reduceCyclically_sublist {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    List.Sublist (FreeGroup.reduceCyclically L) L := by
  have h := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
  have hsub : List.Sublist (FreeGroup.reduceCyclically L)
      (FreeGroup.reduceCyclically.conjugator L ++ FreeGroup.reduceCyclically L ++
        FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L)) :=
    (List.sublist_append_right (FreeGroup.reduceCyclically.conjugator L)
      (FreeGroup.reduceCyclically L)).trans
      (List.sublist_append_left (FreeGroup.reduceCyclically.conjugator L ++
        FreeGroup.reduceCyclically L) (FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L)))
  rw [h] at hsub
  exact hsub

/-- Counting letters different from `t` is monotone under taking sublists. -/
theorem countP_ne_sublist_le {α : Type*} [DecidableEq α] {t : α} {L M : List (α × Bool)}
    (h : List.Sublist L M) :
    L.countP (fun p => decide (p.1 ≠ t)) ≤ M.countP (fun p => decide (p.1 ≠ t)) := by
  have hf := List.Sublist.filter (fun p : α × Bool => decide (p.1 ≠ t)) h
  have hlen := hf.length_le
  rwa [← List.countP_eq_length_filter, ← List.countP_eq_length_filter] at hlen

theorem nonTLetters_cyclicReduction_le {α : Type*} (w : FreeGroup α) (t : α) :
    Work.OROneRel.nonTLetters t (Work.OROneRel.cyclicReduction w) ≤ Work.OROneRel.nonTLetters t w := by
  classical
  have hred : FreeGroup.IsReduced (FreeGroup.reduceCyclically w.toWord) :=
    (FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord).isReduced
  have hreduce_eq : FreeGroup.reduce (FreeGroup.reduceCyclically w.toWord) =
      FreeGroup.reduceCyclically w.toWord :=
    (FreeGroup.isReduced_iff_reduce_eq).mp hred
  have htoWord : (Work.OROneRel.cyclicReduction w).toWord = FreeGroup.reduceCyclically w.toWord := by
    unfold Work.OROneRel.cyclicReduction
    rw [FreeGroup.toWord_mk, hreduce_eq]
  simp only [Work.OROneRel.nonTLetters]
  rw [htoWord]
  exact countP_ne_sublist_le (reduceCyclically_sublist w.toWord)

end Work.OROneRel
