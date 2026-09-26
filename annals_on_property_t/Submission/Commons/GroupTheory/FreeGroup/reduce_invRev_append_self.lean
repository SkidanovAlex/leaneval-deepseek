import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

lemma reduce_invRev_append_self {α : Type*} [DecidableEq α] (W : List (α × Bool))
    (hW : FreeGroup.IsReduced W) :
    FreeGroup.reduce (FreeGroup.invRev W ++ W) = [] := by
  -- The cancellation `invRev W ++ W ↦ ε` holds for *every* word `W`
  -- (Mathlib's `reduce_invRev_left_cancel`); the reducedness hypothesis `hW` is not needed.
  have _hW_used := hW
  exact FreeGroup.reduce_invRev_left_cancel (L := W)

end Commons.GroupTheory.FreeGroup
