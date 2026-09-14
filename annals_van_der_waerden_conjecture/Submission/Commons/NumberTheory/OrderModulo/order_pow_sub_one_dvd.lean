import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.OrderModulo

/-- If `m ∣ p ^ f - 1` (with `2 ≤ p`), then `p` has multiplicative order modulo `m`
dividing `f`.

Indeed `m ∣ p ^ f - 1` says exactly that `(p : ZMod m) ^ f = 1`, and the order of an
element of a monoid divides any exponent with that property. -/
theorem order_pow_sub_one_dvd (p m : ℕ) (hp : 2 ≤ p) (hm : 1 ≤ m) {f : ℕ}
    (hdiv : m ∣ p ^ f - 1) : orderOf (p : ZMod m) ∣ f := by
  have hp0 : 0 < p := by omega
  -- `m ∣ p ^ f - 1` means the natural number `p ^ f - 1` is zero in `ZMod m`.
  have hz : ((p ^ f - 1 : ℕ) : ZMod m) = 0 :=
    (ZMod.natCast_eq_zero_iff (p ^ f - 1) m).2 hdiv
  -- Casting `p ^ f - 1` to `ZMod m` gives `(p : ZMod m) ^ f - 1` (no truncation,
  -- since `1 ≤ p ^ f`).
  have hcast : ((p ^ f - 1 : ℕ) : ZMod m) = (p : ZMod m) ^ f - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow f p hp0), Nat.cast_pow, Nat.cast_one]
  -- Hence `(p : ZMod m) ^ f = 1`.
  have hpow : (p : ZMod m) ^ f = 1 := sub_eq_zero.mp (hcast.symm.trans hz)
  -- The order of an element of a monoid divides any exponent making it `1`.
  exact orderOf_dvd_of_pow_eq_one hpow

end Commons.NumberTheory.OrderModulo