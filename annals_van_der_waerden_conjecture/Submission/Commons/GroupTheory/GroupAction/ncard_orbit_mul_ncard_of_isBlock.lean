import Mathlib.GroupTheory.GroupAction.Blocks

namespace Commons.GroupTheory.GroupAction

open scoped Pointwise

set_option linter.style.haveILetI false in
theorem ncard_orbit_mul_ncard_of_isBlock {G X : Type*} [Group G] [MulAction G X]
    [Finite X] (htrans : MulAction.IsPretransitive G X) {B : Set X} (hB : MulAction.IsBlock G B)
    (hne : B.Nonempty) :
    (MulAction.orbit G B).ncard * B.ncard = Nat.card X := by
  haveI := htrans
  rw [Nat.mul_comm]
  exact hB.ncard_block_mul_ncard_orbit_eq hne

end Commons.GroupTheory.GroupAction