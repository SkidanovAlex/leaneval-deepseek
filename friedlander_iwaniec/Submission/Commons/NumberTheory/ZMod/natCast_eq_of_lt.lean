import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Commons.NumberTheory.ZMod

/-- Distinct naturals below `q` give distinct elements of `ZMod q`. -/
theorem natCast_eq_of_lt {q : ℕ} [NeZero q] {n m : ℕ} (hn : n < q) (hm : m < q) :
    (n : ZMod q) = (m : ZMod q) ↔ n = m := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm]

end Commons.NumberTheory.ZMod