import Mathlib.NumberTheory.Padics.RingHoms
import Submission.Work.QuadraticLocalGlobal.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

/-- The reduction map `ℤ_[p] → ZMod (p ^ n)` is compatible with the cast of integers. -/
theorem toZModPow_intCast {p : ℕ} [Fact p.Prime] (n : ℕ) (m : ℤ) : PadicInt.toZModPow n (m : ℤ_[p]) = (m : ZMod (p ^ n)) := by
  exact map_intCast (PadicInt.toZModPow n) m

end Work.QuadraticLocalGlobal
