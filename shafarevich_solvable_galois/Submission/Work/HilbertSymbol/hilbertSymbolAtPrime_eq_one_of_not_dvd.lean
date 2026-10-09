/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `(a,b)_p = 1` for odd `p` not dividing `a` or `b`
-/
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.padicVal_eq_zero_iff
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- For an odd prime `p` which divides neither the numerator nor the denominator of the rational
representatives of `a` and `b`, the Hilbert symbol `(a,b)_p` is `1`.  Equivalently (since only the
primes dividing `2ab` and the archimedean place can contribute) `p ∤ 2 a b → (a,b)_p = 1`.

This is the `p`-adic "Hensel" computation: `a` and `b` are `p`-adic units, so both valuations
vanish and the explicit formula degenerates to `1`. -/
theorem hilbertSymbolAtPrime_eq_one_of_not_dvd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b : ℚˣ}
    (ha1 : ¬ (p : ℤ) ∣ (a : ℚ).num) (ha2 : ¬ p ∣ (a : ℚ).den)
    (hb1 : ¬ (p : ℤ) ∣ (b : ℚ).num) (hb2 : ¬ p ∣ (b : ℚ).den) :
    hilbertSymbolAtPrime p a b = 1 := by
  rw [hilbertSymbolAtPrime_eq_odd hp,
    hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
      ((padicVal_eq_zero_iff a).mpr ⟨ha1, ha2⟩) ((padicVal_eq_zero_iff b).mpr ⟨hb1, hb2⟩)]

end Work.HilbertSymbol
