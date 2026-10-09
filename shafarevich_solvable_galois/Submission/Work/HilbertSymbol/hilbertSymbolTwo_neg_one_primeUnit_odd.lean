import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.signOf_epsZ_primeUnit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-!
# The Hilbert symbol `(-1, p)_2` for an odd prime `p`

At the place `2`, the Hilbert symbol is
`(a,b)_2 = signOf (ε(u) ε(v) + α ω(v) + β ω(u))`, where `u = unitPart 2 a`, `v = unitPart 2 b`,
`α = v₂(a)`, `β = v₂(b)`, `ε = epsZ` and `ω = omegaZ`.

For `a = -1` and `b = p` an odd prime, both valuations vanish (`v₂(-1) = 0` and `v₂(p) = 0`), so
the formula collapses to `signOf (ε(-1) · ε(p))`.  Since `ε(-1) = 1` (as `-1 ≡ 3 = 1 + 2·1`
modulo `4`) this is `signOf (ε(p))`, and `signOf (ε(p)) = (-1/p)`
(`signOf_epsZ_primeUnit`), the Legendre symbol of `-1` modulo `p`.
-/

/-- `ε(-1) = 1`: the `2`-adic unit part of `-1` is `-1`, which is `3 = 1 + 2·1` modulo `4`. -/
private theorem epsZ_unitPart_two_neg_one : epsZ (unitPart 2 (-1 : ℚˣ)) = 1 := by
  have hpv : padicVal 2 (-1 : ℚˣ) = 0 := by rw [padicVal_neg]; simp
  have hunit : (unitPart 2 (-1 : ℚˣ) : ℤ_[2]) = -1 := by
    apply PadicInt.ext
    rw [unitPart_of_padicVal_eq_zero hpv]
    norm_cast
  rw [epsZ, hunit]
  have hz : PadicInt.toZModPow (p := 2) 2 (-1 : ℤ_[2]) = (-1 : ZMod (2 ^ 2)) := by
    rw [map_neg, map_one]
  rw [hz]
  decide

/-- For an odd prime `p`, the `2`-adic valuation of `p` vanishes. -/
private theorem padicVal_two_primeUnit_of_ne {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
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

/-- **The Hilbert symbol `(-1, p)_2` for an odd prime `p`** equals the Legendre symbol `(-1/p)`.
-/
theorem hilbertSymbolTwo_neg_one_primeUnit_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolTwo (-1 : ℚˣ) (primeUnit p) = intUnitOf (legendreSym p (-1)) := by
  have hval_neg : padicVal 2 (-1 : ℚˣ) = 0 := by rw [padicVal_neg]; simp
  have hval_p : padicVal 2 (primeUnit p) = 0 := padicVal_two_primeUnit_of_ne hp
  have heps : epsZ (unitPart 2 (-1 : ℚˣ)) = 1 := epsZ_unitPart_two_neg_one
  rw [hilbertSymbolTwo, hval_neg, hval_p, heps]
  simp only [Int.cast_zero, zero_mul, add_zero, one_mul]
  exact signOf_epsZ_primeUnit p hp

end Work.HilbertSymbol
