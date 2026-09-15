import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Totient

namespace Commons.Data.Nat

open Finset
open scoped BigOperators

/-- Euler's product formula for the totient function in the form used in Green-Tao section 10:
for `W ≠ 0` the product of `(1 - 1/p)⁻¹` over the prime divisors of `W` equals `W / φ(W)`.
Prove from `Nat.totient_eq_mul_prod_factors` by pushing the identity to `ℂ` via `push_cast`,
then `Finset.prod_inv_distrib`, with `(Nat.totient W : ℂ) ≠ 0` (`Nat.totient_pos`) and
`∏ p ∈ W.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0` (each factor is nonzero since `p ≥ 2`). -/
theorem prod_inv_one_sub_inv_primeFactors (W : ℕ) (hW : W ≠ 0) :
    ∏ p ∈ W.primeFactors, (1 - (p : ℂ)⁻¹)⁻¹ = (W : ℂ) / (Nat.totient W : ℂ) := by
  -- Euler's product formula over ℚ, pushed to ℂ.
  have h := Nat.totient_eq_mul_prod_factors W
  have hC : (Nat.totient W : ℂ) = (W : ℂ) * ∏ p ∈ W.primeFactors, (1 - (p : ℂ)⁻¹) := by
    have h2 := congrArg (fun q : ℚ => (q : ℂ)) h
    push_cast at h2 ⊢
    exact h2
  -- Rewrite the totient and cancel the factor `W`.
  rw [hC]
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  rw [div_mul_eq_div_div, div_self hWc, one_div, Finset.prod_inv_distrib]

end Commons.Data.Nat