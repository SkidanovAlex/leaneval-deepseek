import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem signOf_intCast (n : ℤ) : signOf (n : ZMod 2) = (-1 : ℤˣ) ^ n := by
  rcases Int.even_or_odd n with hn | hn
  · rw [ZMod.intCast_eq_zero_iff_even.mpr hn, signOf_zero, hn.neg_one_zpow]
  · rw [ZMod.intCast_eq_one_iff_odd.mpr hn, signOf_one, hn.neg_one_zpow]

end Work.HilbertSymbol
