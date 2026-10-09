import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.placeProduct_comm
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_primeUnit_distinct_odd
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_self_odd
import Submission.Work.HilbertSymbol.placeProduct_primeUnit_two_odd
import Submission.Work.HilbertSymbol.placeProduct_two_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem placeProduct_primeUnit_primeUnit {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    placeProduct (primeUnit p) (primeUnit q) = 1 := by
  by_cases hp : p = 2
  · subst hp
    by_cases hq : q = 2
    · subst hq
      exact placeProduct_two_two
    · rw [placeProduct_comm]
      exact placeProduct_primeUnit_two_odd hq
  · by_cases hq : q = 2
    · subst hq
      exact placeProduct_primeUnit_two_odd hp
    · by_cases hpq : p = q
      · subst hpq
        exact placeProduct_primeUnit_self_odd hp
      · exact placeProduct_primeUnit_primeUnit_distinct_odd hp hq hpq

end Work.HilbertSymbol
