import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.bandPresentation
import Submission.Work.OROneRel.winRoot_pow

namespace Work.OROneRel

theorem treeKill_walkCell_pow {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (u : FreeGroup α) (l : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (u ^ l)),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    Work.OROneRel.treeKill Wt c lo hi (Work.OROneRel.walkCell c lo hi 0 (u ^ l) hwin) =
      Work.OROneRel.winRoot Wt c lo hi u ^ l := by
  rw [Work.OROneRel.treeKill_walkCell_zero Wt c lo hi (u ^ l) hwin,
    Work.OROneRel.winRoot_pow Wt c lo hi u l hcyc hcu]

end Work.OROneRel
