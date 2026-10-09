import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolOdd_primeUnit (p : ℕ) [Fact p.Prime] (b : ℚˣ)
    (hb : padicVal p b = 0) :
    hilbertSymbolOdd p (primeUnit p) b = legendreOf p b := by
  have hpa : padicVal p (primeUnit p) = 1 := by
    simp [padicVal, primeUnit, ratUnit, padicValRat.self (Fact.out : p.Prime).one_lt]
  unfold hilbertSymbolOdd
  rw [hpa, hb]
  simp

end Work.HilbertSymbol
