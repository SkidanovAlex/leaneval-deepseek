import Mathlib

/-!
# The `p`-adic valuation of `p ^ k * z`

For a prime `p`, multiplying a nonzero integer `z` by `(p : ℤ) ^ k` shifts its
`p`-adic valuation (as measured by `padicValInt p`) up by exactly `k`.

This is the additivity `padicValInt.mul` combined with the computation
`padicValInt p ((p : ℤ) ^ k) = k`.
-/

namespace Work.LinnikBurgess

/-- The `p`-adic valuation of the integer `(p : ℤ) ^ k` is `k`. -/
lemma padicValInt_prime_pow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    padicValInt p ((p : ℤ) ^ k) = k := by
  rw [← Nat.cast_pow, padicValInt.of_nat, padicValNat.prime_pow]

lemma cftValPowMul {p : ℕ} [Fact p.Prime] (k : ℕ) {z : ℤ} (hz : z ≠ 0) :
    padicValInt p ((p : ℤ) ^ k * z) = k + padicValInt p z := by
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padicValInt.mul (pow_ne_zero k hp0) hz, padicValInt_prime_pow]

end Work.LinnikBurgess
