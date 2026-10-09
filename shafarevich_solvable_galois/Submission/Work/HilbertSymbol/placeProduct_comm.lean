import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- Symmetry of the product of the Hilbert symbols over the finite contributing places.  This is
immediate from the symmetry of `contributingPrimes` and of the Hilbert symbol at each finite
place. -/
theorem placeProd_comm (a b : ℚˣ) : placeProd a b = placeProd b a := by
  rw [placeProd, placeProd, contributingPrimes_comm a b]
  exact Finset.prod_congr rfl fun p _ => hilbertSymbol_comm (some p) a b

theorem placeProduct_comm (a b : ℚˣ) : placeProduct a b = placeProduct b a := by
  rw [placeProduct, placeProduct, placeProd_comm a b, hilbertSymbol_comm none a b]

end Work.HilbertSymbol
