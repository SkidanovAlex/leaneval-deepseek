import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.GroupAction.Ring

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.Nat

theorem factorization_two_pow (k : ℕ) : (2 ^ k).factorization 2 = k := by
  rw [Nat.factorization_pow]
  simp [Nat.Prime.factorization_self Nat.prime_two]

end Commons.Nat