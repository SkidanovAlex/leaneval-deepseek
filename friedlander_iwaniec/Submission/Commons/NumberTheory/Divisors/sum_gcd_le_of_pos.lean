import Mathlib
import Submission.Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero
import Submission.Commons.NumberTheory.Gcd.gcd_sum_Icc_le

namespace Commons.NumberTheory.Divisors

open Finset

/-- `∑_{c = 1}^{X} gcd(c, m) ≤ X · τ(m)` for positive `m`: write
`gcd(c,m) = ∑_{e ∣ gcd(c,m)} φ(e)` and count the multiples of `e`.  (The hypothesis `0 < m` is
necessary: for `m = 0` the sum is `X (X+1)/2 > 0 = X · τ(0)`.) -/
theorem sum_gcd_le_of_pos (X m : ℕ) (hm : 0 < m) :
    ∑ c ∈ Finset.Icc 1 X, Nat.gcd c m ≤ X * m.divisors.card := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hstep1 : ∑ c ∈ Finset.Icc 1 X, Nat.gcd c m
      = ∑ c ∈ Finset.Icc 1 X, ∑ k ∈ m.divisors with k ∣ c, Nat.totient k := by
    refine Finset.sum_congr rfl ?_
    intro c _
    exact Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero hm0
  rw [hstep1]
  calc ∑ c ∈ Finset.Icc 1 X, ∑ k ∈ m.divisors with k ∣ c, Nat.totient k
      = ∑ c ∈ Finset.Icc 1 X, ∑ k ∈ m.divisors, if k ∣ c then Nat.totient k else 0 := by
        refine Finset.sum_congr rfl ?_
        intro c _
        rw [Finset.sum_filter]
    _ = ∑ k ∈ m.divisors, ∑ c ∈ Finset.Icc 1 X, if k ∣ c then Nat.totient k else 0 :=
        Finset.sum_comm
    _ ≤ ∑ _k ∈ m.divisors, X := by
        refine Finset.sum_le_sum ?_
        intro k _
        have hinner : ∑ c ∈ Finset.Icc 1 X, (if k ∣ c then Nat.totient k else 0)
            = Nat.totient k * (X / k) := by
          rw [← Finset.sum_filter, Finset.sum_const,
            Commons.NumberTheory.Gcd.card_Icc_one_filter_dvd]
          simp [mul_comm]
        rw [hinner]
        exact le_trans (Nat.mul_le_mul_right (X / k) (Nat.totient_le k)) (Nat.mul_div_le X k)
    _ = X * m.divisors.card := by
        rw [Finset.sum_const]
        simp [mul_comm]

end Commons.NumberTheory.Divisors
