/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hilbert symbol `(p,q)_2` of two odd primes

For odd primes `p` and `q` the Hilbert symbol at the place `2` is

`(p,q)_2 = (-1) ^ ((p-1)/2 * (q-1)/2)`,

i.e. it is `-1` exactly when both `p` and `q` are `3` modulo `4` (equivalently, exactly when both
`2` is a non-residue modulo `p` and modulo `q`).

Proof: since `p` and `q` are odd, their `2`-adic valuation vanishes, so the defining formula of
`hilbertSymbolTwo` reduces to `signOf (ε(p) ε(q))`, and `ε(u) = ((p-1)/2 : ℕ)` in `ZMod 2`
(`epsZ_primeUnit`).  Finally `signOf` of the cast of a natural number `m` into `ZMod 2` is
`(-1)^m` (`signOf_natCast`), and the two casts multiply.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.epsZ_primeUnit
import Submission.Work.HilbertSymbol.signOf_epsZ_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- For an odd prime `p`, the `2`-adic valuation of `p` is `0`; equivalently the `2`-adic unit
part of `p` is `p` itself. -/
theorem padicVal_two_primeUnit {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    padicVal 2 (primeUnit p) = 0 := by
  have h2 : ¬ (2 : ℕ) ∣ p := by
    intro hdvd
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact hp h
    · omega
  rw [padicVal, primeUnit_coe, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd h2]
  norm_num

theorem hilbertSymbolTwo_primeUnit_primeUnit_odd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    hilbertSymbolTwo (primeUnit p) (primeUnit q)
      = (-1 : ℤˣ) ^ ((((p - 1) / 2 : ℕ) * ((q - 1) / 2 : ℕ) : ℕ) : ℤ) := by
  -- Both valuations vanish, so only the `ε`-terms survive in the definition.
  rw [hilbertSymbolTwo, padicVal_two_primeUnit hp, padicVal_two_primeUnit hq,
    epsZ_primeUnit p hp, epsZ_primeUnit q hq]
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero]
  -- `signOf` of the cast of a product of two natural numbers is the corresponding power of `-1`.
  rw [← Nat.cast_mul, signOf_natCast, zpow_natCast]

end Work.HilbertSymbol
