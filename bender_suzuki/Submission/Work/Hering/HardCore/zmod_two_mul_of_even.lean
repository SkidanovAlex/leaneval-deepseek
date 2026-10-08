import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Hering.HardCore

/-- In `ZMod (2 ^ m)`, an element whose canonical representative is even lies in the
image of multiplication by `2`. -/
theorem zmod_two_mul_of_even {m : ℕ} {x : ZMod (2 ^ m)} (h : x.val % 2 = 0) :
    ∃ k : ZMod (2 ^ m), x = 2 * k := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨t, ht⟩ := Nat.dvd_iff_mod_eq_zero.mpr h
  refine ⟨(t : ZMod (2 ^ m)), ?_⟩
  rw [← ZMod.natCast_zmod_val x, ht, Nat.cast_mul]
  norm_num

end Work.Hering.HardCore
