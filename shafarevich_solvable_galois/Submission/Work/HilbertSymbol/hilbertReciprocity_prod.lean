/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hilbert reciprocity in unfolded product form
-/
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.hilbertReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- **Hilbert reciprocity over `ℚ`**, in the unfolded product form: the product of the Hilbert
symbols `(a,b)_p` over the primes dividing `2ab`, times the archimedean symbol, equals `1`. -/
theorem hilbertReciprocity_prod (a b : ℚˣ) :
    (∏ p ∈ contributingPrimes a b, hilbertSymbol (some p) a b) * hilbertSymbol none a b = 1 := by
  rw [← placeProduct_def]
  exact hilbertReciprocity a b

end Work.HilbertSymbol
