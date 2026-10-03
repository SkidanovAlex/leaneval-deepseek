import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.ntDefs

namespace Work.ORLocInd.CohenLyndon

universe u

/-- If the generator `t` does not occur in the reduced word of `v`, then `v` is already a word in
the letters other than `t`: the length norm of `v` equals its `t`-free letter count. -/
theorem relatorNorm_eq_letterCountNot_of_not_mem {α : Type u} (t : α) {v : FreeGroup α}
    (h : t ∉ Work.OROneRel.relatorLetters v) :
    Work.OROneRel.relatorNorm v = Work.OROneRel.letterCountNot t v := by
  classical
  rw [Work.OROneRel.letterCountNot, Work.OROneRel.relatorNorm, FreeGroup.norm]
  refine (List.countP_eq_length.mpr ?_).symm
  intro p hp
  simp only [ne_eq, decide_eq_true_eq]
  intro hpt
  exact h ⟨p.2, hpt ▸ hp⟩

end Work.ORLocInd.CohenLyndon
