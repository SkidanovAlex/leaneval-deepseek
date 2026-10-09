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

/-- The prime `2`, as an element of `ℚˣ`, has `p`-adic valuation `0` at every odd prime `p`. -/
theorem padicVal_primeUnit_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    padicVal p (primeUnit 2) = 0 := by
  have hpdvd : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2
  have hcast : ((primeUnit 2 : ℚˣ) : ℚ) = ((2 : ℕ) : ℚ) := by
    rw [primeUnit_coe]
  rw [padicVal, hcast, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpdvd]
  norm_num

theorem hilbertSymbolOdd_primeUnit_two_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolOdd p (primeUnit p) (primeUnit 2) = intUnitOf (legendreSym p 2) := by
  have hpdvdNat : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2
  have hpdvdInt : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro h
    exact hpdvdNat (Int.natCast_dvd_natCast.mp h)
  have hm : (2 : ℤ) ≠ 0 := by norm_num
  have hpu : primeUnit 2 = intUnit (2 : ℤ) hm :=
    Units.ext (by rw [primeUnit_coe, intUnit_coe]; norm_num)
  rw [hilbertSymbolOdd_primeUnit p (primeUnit 2) (padicVal_primeUnit_two hp)]
  rw [hpu, legendreOf_intUnit hm hpdvdInt]

end Work.HilbertSymbol
