import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Squarefree

namespace Commons.NumberTheory.Nat

/-- If `n` divides a positive power of `m`, then the radical `rad n = ∏_{p | n} p` of `n`
divides `m`. -/
theorem radical_dvd_of_dvd_pow {n m k : ℕ} (hk : 1 ≤ k) (h : n ∣ m ^ k) :
    n.primeFactors.prod id ∣ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero _
  change (∏ p ∈ n.primeFactors, p) ∣ m
  rw [Nat.prod_primeFactors_dvd_iff hm]
  calc n.primeFactors ⊆ (m ^ k).primeFactors := Nat.primeFactors_mono h (pow_ne_zero k hm)
    _ = m.primeFactors := Nat.primeFactors_pow m (by omega)

end Commons.NumberTheory.Nat