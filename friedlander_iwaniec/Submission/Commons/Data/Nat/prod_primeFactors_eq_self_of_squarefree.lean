import Mathlib.Data.Nat.Squarefree

namespace Commons.Data.Nat

theorem prod_primeFactors_eq_self_of_squarefree (d : ℕ) (hd : d ≠ 0) (hsq : Squarefree d) :
    ∏ p ∈ d.primeFactors, p = d := by
  exact Nat.prod_primeFactors_of_squarefree hsq

end Commons.Data.Nat
