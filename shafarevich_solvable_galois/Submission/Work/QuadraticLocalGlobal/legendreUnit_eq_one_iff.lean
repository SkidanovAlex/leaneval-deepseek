import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

/-- For an odd prime `p`, the Legendre symbol `(u / p)` of a `p`-adic unit `u` equals `1`
exactly when the reduction of `u` modulo `p` is a square in `ZMod p`. -/
theorem legendreUnit_eq_one_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (u : ℤ_[p]ˣ) : Work.HilbertSymbol.legendreUnit p u = 1 ↔ IsSquare (PadicInt.toZMod (p := p) (u : ℤ_[p])) := by
  have _hp : p ≠ 2 := hp
  rw [Work.HilbertSymbol.legendreUnit, Work.HilbertSymbol.quadCharUnit,
    Work.HilbertSymbol.intUnitOf_eq_one_iff, Units.coe_map]
  exact (not_congr quadraticChar_neg_one_iff_not_isSquare).trans not_not

end Work.QuadraticLocalGlobal
