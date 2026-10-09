import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-! ## The value of `epsZ` on an odd prime

For an odd prime `p`, the `2`-adic unit part of `p` is `p` itself, and `p ≡ 1 + 2 ε (mod 4)`
with `ε = (p - 1) / 2 mod 2`, i.e. `ε = 0` when `p ≡ 1 (mod 4)` and `ε = 1` when
`p ≡ 3 (mod 4)`.  This is the value `epsZ (unitPart 2 (primeUnit p))` recorded below. -/

theorem epsZ_primeUnit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    epsZ (unitPart 2 (primeUnit p)) = (((p - 1) / 2 : ℕ) : ZMod 2) := by
  -- `p` is odd, so `2` does not divide `p`.
  have hnotdvd : ¬ (2 : ℤ) ∣ (p : ℤ) := by
    intro hdvd
    have h2dvd : 2 ∣ p := by exact_mod_cast hdvd
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact hp h
    · omega
  -- hence the `2`-adic valuation of `p` vanishes.
  have hpv : padicVal 2 (primeUnit p) = 0 := by
    rw [padicVal,
      show ((primeUnit p : ℚˣ) : ℚ) = ((p : ℤ) : ℚ) by simp [primeUnit, ratUnit],
      padicValRat.of_int]
    simpa using padicValInt.eq_zero_of_not_dvd hnotdvd
  -- so the `2`-adic unit part of `p` is `p`.
  have h2 : (unitPart 2 (primeUnit p) : ℤ_[2]) = (p : ℤ_[2]) := by
    apply PadicInt.ext
    rw [unitPart_of_padicVal_eq_zero hpv]
    norm_cast
  -- reducing modulo `4`, `epsZ` reads off `(p mod 4) / 2`, which is `(p - 1) / 2 mod 2`.
  rw [epsZ, h2, map_natCast, ZMod.val_natCast]
  rw [ZMod.natCast_eq_natCast_iff']
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  omega

end Work.HilbertSymbol
