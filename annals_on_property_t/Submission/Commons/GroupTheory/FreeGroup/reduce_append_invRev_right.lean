import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

lemma reduce_append_invRev_right {α : Type*} [DecidableEq α]
    (L : List (α × Bool)) : FreeGroup.reduce (L ++ FreeGroup.invRev L) = [] := by
  simpa [FreeGroup.invRev_invRev] using
    (FreeGroup.reduce_invRev_left_cancel (L := FreeGroup.invRev L))

end Commons.GroupTheory.FreeGroup