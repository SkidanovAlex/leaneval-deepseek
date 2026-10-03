import Mathlib
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewrite_isReduced

namespace Work.ORLyndon

/-- The Magnus rewriting `rewrite t u.toWord` of the reduced word of `u` is an honest representative
of the relator `magRewRel t u`: since it is already reduced, `toWord (magRewRel t u)` is exactly
`mmList t u`.  (The `DecidableEq` instance of the outer `toWord` is pinned to the classical one,
which is the instance used inside the definition of `relatorLetters`.) -/
theorem toWord_magRewRel_eq_mmList {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α) :
    @FreeGroup.toWord ({a : α // a ≠ t} × ℤ) (Classical.decEq _)
      (Work.OROneRel.magRewRel t u) = Work.OROneRel.mmList t u := by
  classical
  have hred : FreeGroup.IsReduced
      (Work.OROneRel.rewrite t (@FreeGroup.toWord α (Classical.decEq α) u)) :=
    Work.OROneRel.rewrite_isReduced t (@FreeGroup.isReduced_toWord α (Classical.decEq α) u)
  rw [Work.OROneRel.mmList, Work.OROneRel.magRew_zero_eq_rewrite]
  rw [Work.OROneRel.magRewRel]
  exact @FreeGroup.IsReduced.reduce_eq _ _ (Classical.decEq _) hred

/-- Membership in `relatorLetters (magRewRel t u)` is exactly membership in the decorating set
`mmDecs t u x`: a generator `(x, j)` of `F((α \ {t}) × ℤ)` occurs in `magRewRel t u` if and only if
the decoration `j` is attached to some occurrence of `x` in the Magnus rewriting `mmList t u`. -/
theorem mem_relatorLetters_magRewRel_iff {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    (p : {a : α // a ≠ t}) (j : ℤ) :
    ((p, j) : ({a : α // a ≠ t} × ℤ)) ∈
        Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u)
      ↔ j ∈ Work.OROneRel.mmDecs t u p := by
  classical
  rw [Work.OROneRel.relatorLetters, Set.mem_ofPred_eq, Work.OROneRel.mem_mmDecs_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (toWord_magRewRel_eq_mmList t u) ▸ hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (toWord_magRewRel_eq_mmList t u).symm ▸ hb⟩

/-- An occurrence of the letter `x` in `u` produces a decoration of `x` in `mmList t u`, so
`mmDecs t u x` is nonempty. -/
theorem mmDecs_nonempty_of_mem_relatorLetters {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    (x : {a : α // a ≠ t}) (hx : (x : α) ∈ Work.OROneRel.relatorLetters u) :
    (Work.OROneRel.mmDecs t u x).Nonempty := by
  classical
  rw [Work.OROneRel.relatorLetters, Set.mem_ofPred_eq] at hx
  obtain ⟨b, hb⟩ := hx
  obtain ⟨p, hp1, hp2⟩ := Work.OROneRel.rewrite_mem_letter t (x : α) x.2 b hb
  have hp : p ∈ Work.OROneRel.mmList t u := by
    rw [Work.OROneRel.mmList, Work.OROneRel.magRew_zero_eq_rewrite]; exact hp2
  have hpe : p = ((x, p.1.2), p.2) := by
    refine Prod.ext ?_ rfl
    refine Prod.ext ?_ rfl
    rw [hp1]
  refine ⟨p.1.2, (Work.OROneRel.mem_mmDecs_iff t u x p.1.2).mpr ⟨p.2, ?_⟩⟩
  rwa [← hpe]

theorem mmHi_mem_relatorLetters {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    (x : {a : α // a ≠ t}) (hx : (x : α) ∈ Work.OROneRel.relatorLetters u) :
    ((x, Work.OROneRel.mmHi t u x) : ({a : α // a ≠ t} × ℤ)) ∈
        Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u) ∧
      ∀ j : ℤ, ((x, j) : ({a : α // a ≠ t} × ℤ)) ∈
        Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u) →
          j ≤ Work.OROneRel.mmHi t u x := by
  classical
  have hne : (Work.OROneRel.mmDecs t u x).Nonempty :=
    mmDecs_nonempty_of_mem_relatorLetters t u x hx
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := Work.OROneRel.exists_mmHi t u hne
    exact (mem_relatorLetters_magRewRel_iff t u x (Work.OROneRel.mmHi t u x)).mpr
      ((Work.OROneRel.mem_mmDecs_iff t u x (Work.OROneRel.mmHi t u x)).mpr ⟨b, hb⟩)
  · intro j hj
    have hjmem : j ∈ Work.OROneRel.mmDecs t u x :=
      (mem_relatorLetters_magRewRel_iff t u x j).mp hj
    rw [Work.OROneRel.mmHi, dif_pos ⟨j, hjmem⟩]
    exact Finset.le_max' _ _ hjmem

end Work.ORLyndon
