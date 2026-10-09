import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_iff
import Submission.Work.QuadraticLocalGlobal.legendreUnit_eq_one_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

theorem valuation_ratCast_padic {p : ℕ} [Fact p.Prime] (x : ℚˣ) :
    ((x : ℚ_[p])).valuation = Work.HilbertSymbol.padicVal p x := by
  rw [Work.HilbertSymbol.padicVal, Padic.valuation_ratCast]

theorem toZMod_padicUnitOf_eq_toZMod_unitPart {p : ℕ} [Fact p.Prime] (x : ℚˣ) :
    PadicInt.toZMod (p := p) ((padicUnitOf p (x : ℚ_[p]) (ratCast_ne_zero x) : ℤ_[p])) =
    PadicInt.toZMod (p := p) ((unitPart p x : ℤ_[p])) := by
  congr 1
  apply PadicInt.ext
  rw [padicUnitOf_coe, unitPart_coe, unitVal, valuation_ratCast_padic]

theorem isSquare_padic_rat_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (x : ℚˣ) : IsSquare ((x : ℚ_[p])) ↔ Even (Work.HilbertSymbol.padicVal p x) ∧ Work.HilbertSymbol.legendreOf p x = 1 := by
  rw [isSquare_padic_iff hp (ratCast_ne_zero x), toZMod_padicUnitOf_eq_toZMod_unitPart (p := p) x,
    valuation_ratCast_padic x, ← legendreUnit_eq_one_iff hp (unitPart p x)]
  rfl

end Work.QuadraticLocalGlobal
