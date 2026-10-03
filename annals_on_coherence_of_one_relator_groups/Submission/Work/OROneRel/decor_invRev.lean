import Mathlib
import Submission.Work.OROneRel.delWordDefs
import Submission.Work.OROneRel.exists_treeGauge
import Submission.Work.OROneRel.decor_invRev_flip

namespace Work.OROneRel

universe u

/-- Reading `L` backwards from level `a + lsig c L` (so that the running levels of the reversed
word are the mirror image of those of `L` started at `a`) decorates the letters in reverse order
with the booleans flipped.  This is `decor_invRev_flip` with `i = a + lsig c L`, using
`(a + lsig c L) - lsig c L = a`. -/
theorem decor_invRev {α : Type u} (c : α → ℤ) (a : ℤ) (L : List (α × Bool)) : Work.OROneRel.decor c (a + Work.OROneRel.lsig c L) (FreeGroup.invRev L) = ((Work.OROneRel.decor c a L).reverse.map fun p => (p.1, !p.2)) := by
  rw [decor_invRev_flip c (a + lsig c L) L]
  simp only [add_sub_cancel_right]

end Work.OROneRel
