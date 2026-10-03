import Mathlib

-- The workspace sets `autoImplicit = false`, so the universe `u` occurring in the statement
-- below must be declared explicitly (the statement itself is unchanged).
universe u

namespace Work.ORLyndon

theorem lift_eq_self_of_toWord {α : Type u} [DecidableEq α] {f : α → FreeGroup α} {w : FreeGroup α}
    (hf : ∀ c ∈ FreeGroup.toWord w, f c.1 = FreeGroup.of c.1) : FreeGroup.lift f w = w := by
  -- It suffices to compare `lift f` with `lift of` on the reduced word `toWord w`,
  -- since `w = mk (toWord w)` and `lift of` is the identity on the free group.
  have key : FreeGroup.lift f (FreeGroup.mk (FreeGroup.toWord w))
      = FreeGroup.lift FreeGroup.of (FreeGroup.mk (FreeGroup.toWord w)) := by
    rw [FreeGroup.lift_mk, FreeGroup.lift_mk]
    congr 1
    apply List.map_congr_left
    intro x hx
    rw [hf x hx]
  rwa [FreeGroup.mk_toWord, FreeGroup.lift_of_apply] at key

end Work.ORLyndon
