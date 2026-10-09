import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The supplementary law `(-1/p) = (-1)^{(p-1)/2}` for an odd prime `p`, expressed in the
`ℤˣ`-valued form used by the Hilbert symbol at the finite places. -/
theorem intUnitOf_legendreSym_neg_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    intUnitOf (legendreSym p (-1)) = (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  have hdiv : p / 2 = (p - 1) / 2 := by
    have hn : p = 2 * (p / 2) + 1 := by
      have := Nat.div_add_mod p 2
      omega
    omega
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow hodd, hdiv]
  have hpow : intUnitOf ((-1 : ℤ) ^ ((p - 1) / 2)) = (-1 : ℤˣ) ^ ((p - 1) / 2) := by
    rcases Nat.even_or_odd ((p - 1) / 2) with h | h
    · rw [h.neg_one_pow, intUnitOf_one, h.neg_one_pow]
    · rw [h.neg_one_pow, intUnitOf_neg_one, h.neg_one_pow]
  rw [hpow, zpow_natCast]

theorem hilbertSymbolOdd_primeUnit_self_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolOdd p (primeUnit p) (primeUnit p) = intUnitOf (legendreSym p (-1)) := by
  rw [hilbertSymbolOdd_primeUnit_self p hp]
  exact (intUnitOf_legendreSym_neg_one hp).symm

end Work.HilbertSymbol
