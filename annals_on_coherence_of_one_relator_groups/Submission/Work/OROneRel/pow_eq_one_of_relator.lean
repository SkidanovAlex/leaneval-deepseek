import Mathlib
import Submission.Work.OROneRel.Basic

universe u

namespace Work.OROneRel

/-- If the relator `r` of the one-relator presentation `⟨α | r⟩` is an `l`-th power `u ^ l`,
then the image of `u` in `⟨α | r⟩` has order dividing `l`. -/
theorem pow_eq_one_of_relator {α : Type u} (r u : FreeGroup α) (l : ℕ) (hr : r = u ^ l) :
    (PresentedGroup.mk ({r} : Set (FreeGroup α)) u) ^ l = 1 := by
  rw [← map_pow (PresentedGroup.mk ({r} : Set (FreeGroup α))) u l, ← hr]
  exact PresentedGroup.one_of_mem (Set.mem_singleton r)

end Work.OROneRel
