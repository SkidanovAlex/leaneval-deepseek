import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- If `L` is a reduced word, the maximal reduction of `FreeGroup.mk L` is `L` itself. -/
theorem toWord_mk_of_isReduced {α : Type u} [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.IsReduced L) :
    FreeGroup.toWord (FreeGroup.mk L) = L := by
  rw [FreeGroup.toWord_mk, h.reduce_eq]

theorem isCyclicallyReducedRelator_mk {α : Type u} {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    Work.OROneRel.IsCyclicallyReducedRelator (FreeGroup.mk L) := by
  classical
  unfold Work.OROneRel.IsCyclicallyReducedRelator
  rw [FreeGroup.toWord_mk, h.isReduced.reduce_eq]
  exact h

end Work.OROneRel
