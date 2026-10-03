import Mathlib
import Submission.Work.OROneRel.delWordWalkDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The weight of a cons: the increment of the head plus the weight of the tail. -/
private theorem delWordAt_append_lsig_cons (c : α → ℤ) (p : α × Bool) (L : List (α × Bool)) :
    lsig c (p :: L) = linc c p + lsig c L := by
  obtain ⟨x, b⟩ := p
  cases b <;> simp [lsig, linc]

theorem delWordAt_append (T : Set (α × ℤ)) (c : α → ℤ) (a : ℤ) (L₁ L₂ : List (α × Bool)) :
    Work.OROneRel.delWordAt T c a (L₁ ++ L₂) =
      Work.OROneRel.delWordAt T c a L₁ ++
        Work.OROneRel.delWordAt T c (a + Work.OROneRel.lsig c L₁) L₂ := by
  induction L₁ generalizing a with
  | nil =>
    have h1 : delWordAt T c a ([] : List (α × Bool)) = [] := by unfold delWordAt; rfl
    rw [List.nil_append, h1, List.nil_append]
    congr 1
    rw [show lsig c ([] : List (α × Bool)) = 0 from rfl, add_zero]
  | cons p L ih =>
    rw [List.cons_append]
    have hshift : a + lsig c (p :: L) = a + linc c p + lsig c L := by
      rw [delWordAt_append_lsig_cons]; ring
    by_cases h : coverEdge (trav c a p) ∈ T
    · rw [delWordAt_cons_of_mem T c a p (L ++ L₂) h,
          delWordAt_cons_of_mem T c a p L h, hshift]
      exact ih (a + linc c p)
    · rw [delWordAt_cons_of_notMem T c a p (L ++ L₂) h,
          delWordAt_cons_of_notMem T c a p L h, hshift]
      rw [List.cons_append, ih (a + linc c p)]

end Work.OROneRel
