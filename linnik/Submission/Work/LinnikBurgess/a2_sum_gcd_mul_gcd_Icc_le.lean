import Mathlib
import Submission.Work.LinnikBurgess.a2_gcdmul
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos

/-!
# The `a2`-sum bound `∑_{c ≤ N} gcd(m,c)·gcd(d,c) ≤ N·τ(m)·τ(d)`

For coprime positive `m`, `d` the product of the two `gcd`-weights at `c` is at most
`gcd (m*d) c` (`Work.LinnikBurgess.gcd_mul_gcd_le_gcd_mul`), so the sum is bounded by
`∑_{c ≤ N} gcd (m*d) c`, which the divisor-counting bound
`Commons.NumberTheory.Divisors.sum_gcd_le_of_pos` controls by `N·τ(m*d)`.  Coprimality of `m`
and `d` upgrades `τ(m*d)` to `τ(m)·τ(d)` via `Nat.Coprime.card_divisors_mul`.
-/

namespace Work.LinnikBurgess

theorem a2_sum_gcd_mul_gcd_Icc_le {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (hmd : Nat.Coprime m d)
    (N : ℕ) :
    (∑ c ∈ Finset.Icc 1 N, (Nat.gcd m c : ℝ) * (Nat.gcd d c : ℝ))
      ≤ (N : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ)) := by
  have hmd0 : 0 < m * d := Nat.mul_pos hm hd
  -- Step 1: pointwise bound `gcd m c * gcd d c ≤ gcd (m*d) c`.
  have hpoint : ∀ c ∈ Finset.Icc 1 N,
      (Nat.gcd m c : ℝ) * (Nat.gcd d c : ℝ) ≤ (Nat.gcd (m * d) c : ℝ) := by
    intro c _
    exact_mod_cast gcd_mul_gcd_le_gcd_mul hm hd hmd (n := c)
  have hsum1 : (∑ c ∈ Finset.Icc 1 N, (Nat.gcd m c : ℝ) * (Nat.gcd d c : ℝ))
      ≤ ∑ c ∈ Finset.Icc 1 N, (Nat.gcd (m * d) c : ℝ) :=
    Finset.sum_le_sum hpoint
  -- Step 2: the divisor-counting bound in `ℕ`, cast to `ℝ`.
  have hnat : ∑ c ∈ Finset.Icc 1 N, Nat.gcd c (m * d) ≤ N * (m * d).divisors.card :=
    Commons.NumberTheory.Divisors.sum_gcd_le_of_pos N (m * d) hmd0
  have hsum2 : (∑ c ∈ Finset.Icc 1 N, (Nat.gcd (m * d) c : ℝ))
      ≤ (N : ℝ) * ((m * d).divisors.card : ℝ) := by
    have h1 : (∑ c ∈ Finset.Icc 1 N, (Nat.gcd (m * d) c : ℝ))
        = ((∑ c ∈ Finset.Icc 1 N, Nat.gcd (m * d) c : ℕ) : ℝ) := (Nat.cast_sum _ _).symm
    rw [h1]
    have h2 : (∑ c ∈ Finset.Icc 1 N, Nat.gcd (m * d) c : ℕ)
        = ∑ c ∈ Finset.Icc 1 N, Nat.gcd c (m * d) :=
      Finset.sum_congr rfl (fun c _ => Nat.gcd_comm _ _)
    rw [h2]
    exact_mod_cast hnat
  -- Step 3: `τ(m*d) = τ(m)*τ(d)` for coprime `m`, `d`.
  have hcard : (m * d).divisors.card = m.divisors.card * d.divisors.card :=
    Nat.Coprime.card_divisors_mul hmd
  calc (∑ c ∈ Finset.Icc 1 N, (Nat.gcd m c : ℝ) * (Nat.gcd d c : ℝ))
      ≤ ∑ c ∈ Finset.Icc 1 N, (Nat.gcd (m * d) c : ℝ) := hsum1
    _ ≤ (N : ℝ) * ((m * d).divisors.card : ℝ) := hsum2
    _ = (N : ℝ) * ((m.divisors.card : ℝ) * (d.divisors.card : ℝ)) := by
        rw [hcard, Nat.cast_mul]

end Work.LinnikBurgess
