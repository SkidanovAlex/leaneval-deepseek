import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalTame.IndexPrime

/-- If `ℓ` is a prime which is zero in a ring `R` (i.e. `R` has characteristic `ℓ`, or `R` is
trivial), then for every `x : R` and every `j : ℕ` the Frobenius power map satisfies
`(x - 1) ^ (ℓ ^ j) = x ^ (ℓ ^ j) - 1`.

This is the iterated form of the freshman's dream identity `(a - 1) ^ ℓ = a ^ ℓ - 1`. -/
theorem sub_one_pow_prime_pow {R : Type*} [Ring R] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓR : (ℓ : R) = 0) (x : R) (j : ℕ) : (x - 1) ^ (ℓ ^ j) = x ^ (ℓ ^ j) - 1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · -- In the nontrivial case `(ℓ : R) = 0` determines the characteristic, and the iterated
    -- Frobenius identity for `sub_pow_char_pow_of_commute` applies to `x` and the central `1`.
    have hN : Nontrivial R := hR
    have hF : Fact ℓ.Prime := ⟨hℓ⟩
    have hC : CharP R ℓ := (CharP.charP_iff_prime_eq_zero hℓ).mpr hℓR
    rw [sub_pow_char_pow_of_commute ℓ j (Commute.one_right x), one_pow]

end NK.LocalTame.IndexPrime
