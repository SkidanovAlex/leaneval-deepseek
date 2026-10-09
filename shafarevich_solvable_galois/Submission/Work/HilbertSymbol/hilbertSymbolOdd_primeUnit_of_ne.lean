import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit
import Submission.Work.HilbertSymbol.legendreOf_intUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolOdd_primeUnit_of_ne {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) :
    hilbertSymbolOdd p (primeUnit p) (primeUnit q) = intUnitOf (legendreSym p q) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hpu : primeUnit q = intUnit (q : ℤ) hq0 := by
    apply Units.ext
    simp [primeUnit, intUnit, ratUnit]
  have hndvd : ¬ (p : ℤ) ∣ (q : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    exact hpq ((Nat.Prime.dvd_iff_eq (Fact.out : q.Prime)
      (Fact.out : p.Prime).ne_one).mp h).symm
  have hval : padicVal p (primeUnit q) = 0 := by
    rw [hpu]
    exact padicVal_intUnit hq0 hndvd
  rw [hilbertSymbolOdd_primeUnit p (primeUnit q) hval, hpu, legendreOf_intUnit hq0 hndvd]

end Work.HilbertSymbol
