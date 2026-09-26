import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

/-- Reduction is compatible with concatenation: reducing `X ++ Y` directly gives the
same word as first reducing `X` and `Y` separately and then reducing the concatenation
of the two reduced words. -/
lemma reduce_append_reduce {α : Type*} [DecidableEq α] (X Y : List (α × Bool)) :
    FreeGroup.reduce (X ++ Y) = FreeGroup.reduce (FreeGroup.reduce X ++ FreeGroup.reduce Y) := by
  -- `X ++ Y` reduces to `reduce X ++ reduce Y` via the reductions of `X` and `Y`.
  -- Words that reduce to each other have equal maximal reductions.
  apply FreeGroup.reduce.eq_of_red
  exact FreeGroup.Red.append_append (FreeGroup.reduce.red (L := X)) (FreeGroup.reduce.red (L := Y))

end Commons.GroupTheory.FreeGroup
