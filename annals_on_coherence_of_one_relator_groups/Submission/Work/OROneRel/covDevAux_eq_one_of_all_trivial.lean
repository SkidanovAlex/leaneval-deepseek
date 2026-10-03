import Mathlib
import Submission.Work.OROneRel.covCollapseDefs

namespace Work.OROneRel

/-- **The development is trivial when every traversed edge has trivial loop class.**

`covDevAux W c i L` is the ordered product, over the decorated letters `p` of `decor c i L`, of the
symbols `covDevSym W c (coverEdge p) b`.  Each such symbol is `1` as soon as the edge `coverEdge p`
has trivial loop class, so if every edge occurring in the decoration of `L` has trivial class, the
whole development collapses to `1`. -/
theorem covDevAux_eq_one_of_forall_mem {α : Type*} (W : ℤ → FreeGroup α) (c : α → ℤ)
    (L : List (α × Bool)) (i : ℤ)
    (h : ∀ e ∈ decor c i L, coverClassAt W c (coverEdge e) = 1) :
    covDevAux W c i L = 1 := by
  induction L generalizing i with
  | nil => exact covDevAux_nil W c i
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [covDevAux_cons_false]
      have hhead : coverClassAt W c (a, i - c a) = 1 :=
        h ((a, i - c a), false) (by simp [decor])
      have htail : ∀ e ∈ decor c (i - c a) L, coverClassAt W c (coverEdge e) = 1 := by
        intro e he
        exact h e (by simp [decor, he])
      rw [covDevSym_false_of_eq W c (a, i - c a) hhead, ih (i - c a) htail, one_mul]
    · rw [covDevAux_cons_true]
      have hhead : coverClassAt W c (a, i) = 1 :=
        h ((a, i), true) (by simp [decor])
      have htail : ∀ e ∈ decor c (i + c a) L, coverClassAt W c (coverEdge e) = 1 := by
        intro e he
        exact h e (by simp [decor, he])
      rw [covDevSym_true_of_eq W c (a, i) hhead, ih (i + c a) htail, one_mul]

theorem covDevAux_eq_one_of_all_trivial {α : Type*} (W : ℤ → FreeGroup α) (c : α → ℤ)
    (L : List (α × Bool)) (i : ℤ)
    (h : ∀ e ∈ Work.OROneRel.decor c i L, Work.OROneRel.coverClassAt W c (Work.OROneRel.coverEdge e) = 1) :
    Work.OROneRel.covDevAux W c i L = 1 :=
  covDevAux_eq_one_of_forall_mem W c L i h

end Work.OROneRel
