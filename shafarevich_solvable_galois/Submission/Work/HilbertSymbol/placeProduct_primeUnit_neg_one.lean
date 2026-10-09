import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.placeProduct_comm
import Submission.Work.HilbertSymbol.placeProduct_neg_one_primeUnit_odd
import Submission.Work.HilbertSymbol.placeProduct_neg_one_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The place product `∏_v (p, -1)_v` equals `1` for every prime `p`: by symmetry of the Hilbert
symbol this is the already established identity `∏_v (-1, p)_v = 1`, which holds for `p = 2` and
for odd `p`. -/
theorem placeProduct_primeUnit_neg_one {p : ℕ} [Fact p.Prime] :
    placeProduct (primeUnit p) (-1 : ℚˣ) = 1 := by
  rw [placeProduct_comm]
  by_cases hp : p = 2
  · subst hp; exact placeProduct_neg_one_two
  · exact placeProduct_neg_one_primeUnit_odd hp

end Work.HilbertSymbol
