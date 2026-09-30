import Mathlib
import Submission.Work.BMF.recursion.ShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

lemma shiftMod_inj (p k y m n : ℕ) (hp : p.Prime) (hm : m < p ^ k) (hn : n < p ^ k)
    (h : Work.BMF.recursion.shiftMod p k y m = Work.BMF.recursion.shiftMod p k y n) : m = n := by
  have hm1 := shiftMod_modEq p k y m hp
  have hn1 := shiftMod_modEq p k y n hp
  rw [h] at hm1
  -- both `m - y` and `n - y` are congruent to the common value `shiftMod p k y n`
  have h3 : ((m : ℤ) - (y : ℤ)) ≡ ((n : ℤ) - (y : ℤ)) [ZMOD (p : ℤ) ^ k] := hm1.symm.trans hn1
  have h4 : (m : ℤ) ≡ (n : ℤ) [ZMOD (p : ℤ) ^ k] := by
    have := h3.add_right (y : ℤ)
    simpa using this
  rw [show (p : ℤ) ^ k = ((p ^ k : ℕ) : ℤ) from (Nat.cast_pow p k).symm] at h4
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h4) hm hn

end Work.BMF.recursion
