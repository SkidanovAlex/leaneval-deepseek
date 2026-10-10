import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.Tactic.NormNum.Eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

/-- If `ℓ ^ (2 * k)` divides `x ^ 2` then `ℓ ^ k` divides `x`.  This is the special case
`a = ℓ ^ k`, `n = 2` of the general UFD fact `a ^ n ∣ b ^ n ↔ a ∣ b` (`n ≠ 0`), using
`(ℓ ^ k) ^ 2 = ℓ ^ (2 * k)`.  Primality of `ℓ` is not actually needed for the implication,
but is part of the requested statement. -/
theorem prime_pow_dvd_of_pow_dvd_sq {ℓ x k : ℕ} (hℓ : ℓ.Prime) (h : ℓ ^ (2 * k) ∣ x ^ 2) :
    ℓ ^ k ∣ x := by
  have h' : (ℓ ^ k) ^ 2 ∣ x ^ 2 := by
    rwa [← pow_mul, mul_comm]
  exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp h'

end NK.TameStructureDeep.Tame
