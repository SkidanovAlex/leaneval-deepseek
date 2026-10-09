/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The contributing primes of a pair of prime units

For primes `p` and `q`, the only finite places at which the Hilbert symbol `(p, q)_v` can be
different from `1` are the prime `2` and the two primes `p` and `q` themselves.  This file
identifies `contributingPrimes (primeUnit p) (primeUnit q)` with `{2, p, q}`.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem contributingPrimes_primeUnit {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    contributingPrimes (primeUnit p) (primeUnit q) = insert 2 ({p, q} : Finset ℕ) := by
  rw [contributingPrimes, primeFactors_numDenNat_primeUnit p, primeFactors_numDenNat_primeUnit q]
  simp [Finset.singleton_union]

end Work.HilbertSymbol
