import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Hering.HardCore

/-- In `ZMod (2 ^ m)`, an element whose canonical representative is odd is a unit. -/
theorem zmod_unit_of_odd {m : ℕ} {x : ZMod (2 ^ m)} (h : x.val % 2 = 1) :
    ∃ y : ZMod (2 ^ m), x * y = 1 := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hodd : Odd x.val := Nat.odd_iff.mpr h
  have hcop : Nat.Coprime x.val (2 ^ m) := by
    obtain rfl | hm := eq_or_ne m 0
    · simp
    · rw [Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hm)]
      exact Odd.coprime_two_right hodd
  have hunit : IsUnit x := by
    rw [← ZMod.natCast_zmod_val x]
    exact (ZMod.isUnit_iff_coprime x.val (2 ^ m)).mpr hcop
  exact IsUnit.exists_right_inv hunit

end Work.Hering.HardCore
