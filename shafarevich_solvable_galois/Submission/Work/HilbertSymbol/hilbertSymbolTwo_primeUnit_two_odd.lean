import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.signOf_omegaZ_primeUnit
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-! ## Auxiliary evaluations of `epsZ`, `omegaZ` and `padicVal` -/

/-- `epsZ` of the trivial unit vanishes. -/
theorem epsZ_one : epsZ (1 : ℤ_[2]ˣ) = 0 := by
  simp only [epsZ, Units.val_one, map_one]
  rw [show (1 : ZMod (2 ^ 2)) = ((1 : ℕ) : ZMod (2 ^ 2)) by norm_num, ZMod.val_natCast]
  norm_num

/-- `omegaZ` of the trivial unit vanishes. -/
theorem omegaZ_one : omegaZ (1 : ℤ_[2]ˣ) = 0 := by
  simp only [omegaZ, Units.val_one, map_one]
  rw [show (1 : ZMod (2 ^ 3)) = ((1 : ℕ) : ZMod (2 ^ 3)) by norm_num, ZMod.val_natCast]
  norm_num

/-- For an odd prime `p`, the `2`-adic valuation of `p` vanishes. -/
theorem padicVal_two_primeUnit_of_ne {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    padicVal 2 (primeUnit p) = 0 := by
  rw [padicVal, primeUnit_coe, padicValRat.of_nat]
  have h2 : padicValNat 2 p = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · omega
  rw [h2]
  norm_num

/-- The Hilbert symbol `(p, 2)_2` at the prime `2` for an odd prime `p` reduces to the sign
of `omegaZ` of the `2`-adic unit part of `p`. -/
theorem hilbertSymbolTwo_primeUnit_two_eq_signOf_omegaZ {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolTwo (primeUnit p) (primeUnit 2) =
      signOf (omegaZ (unitPart 2 (primeUnit p))) := by
  have hpv : padicVal 2 (primeUnit p) = 0 := padicVal_two_primeUnit_of_ne hp
  rw [hilbertSymbolTwo, hpv, padicVal_primeUnit 2, unitPart_primeUnit 2, epsZ_one, omegaZ_one]
  simp

/-- **Shafarevich, auxiliary computation.** For an odd prime `p`, the quadratic Hilbert symbol
`(p, 2)_2` at the prime `2` equals the Legendre symbol `(2/p)`. -/
theorem hilbertSymbolTwo_primeUnit_two_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolTwo (primeUnit p) (primeUnit 2) = intUnitOf (legendreSym p 2) := by
  rw [hilbertSymbolTwo_primeUnit_two_eq_signOf_omegaZ hp]
  exact signOf_omegaZ_primeUnit p hp

end Work.HilbertSymbol
