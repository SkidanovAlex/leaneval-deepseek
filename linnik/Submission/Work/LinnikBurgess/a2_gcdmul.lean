import Mathlib

/-!
# A `gcd` product inequality for coprime arguments

If `m` and `d` are coprime then `gcd m n * gcd d n ≤ gcd (m * d) n` (in fact the two sides are
equal, but only the inequality is needed).  This is the only number-theoretic input to the
`a2`-sum bound: it converts the product of the two weights into a single `gcd`, to which the
divisor-counting bound `Commons.NumberTheory.Divisors.sum_gcd_le_of_pos` applies.
-/

namespace Work.LinnikBurgess

/-- For coprime `m`, `d` the product of the `gcd`s with `n` is at most the `gcd` with the
product. -/
theorem gcd_mul_gcd_le_gcd_mul {m d n : ℕ} (hm : 0 < m) (hd : 0 < d) (h : m.Coprime d) :
    Nat.gcd m n * Nat.gcd d n ≤ Nat.gcd (m * d) n := by
  refine Nat.le_of_dvd (Nat.gcd_pos_of_pos_left n (Nat.mul_pos hm hd)) ?_
  refine Nat.dvd_gcd ?_ ?_
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left m n) (Nat.gcd_dvd_left d n)
  · exact ((h.coprime_dvd_left (Nat.gcd_dvd_left m n)).coprime_dvd_right
      (Nat.gcd_dvd_left d n)).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right m n)
      (Nat.gcd_dvd_right d n)

end Work.LinnikBurgess
