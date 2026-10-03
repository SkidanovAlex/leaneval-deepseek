import Mathlib
import Submission.Work.FIArea2.NsolDefs

namespace Work.FIArea2

/-- **`Jsum` at a prime power.**  For any prime `p` and `ν ≥ 0`, the divisor sum of (8.13) at `q = p^ν` is the geometric sum `p^ν Σ_{α=0}^{ν} (φ(p^α)/p^α)(a/p)^α`: the divisors of `p^ν` are `p^0, …, p^ν` (`Nat.divisors_prime_pow`), `φ(p^α)` is `Nat.totient_prime_pow`, and `(a/p^α) = (a/p)^α` is `jacobiSym.pow_right`.  This is the "we write `⌊ν/2⌋ + ⌊(ν+1)/2⌋(a/p) = (a/p) + … + (a/p)^ν`" step of the paper, converting their local factor (8.10) into the global form (8.13). -/
theorem Jsum_prime_pow (a : ℤ) (p ν : ℕ) (hp : p.Prime) :
    Jsum (p ^ ν) a = (p : ℝ) ^ ν * ∑ α ∈ Finset.range (ν + 1),
      ((Nat.totient (p ^ α) : ℝ) / ((p : ℝ) ^ α)) * (jacobiSym a p : ℝ) ^ α := by
  rw [Jsum, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Nat.cast_pow, Function.Embedding.coeFn_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [jacobiSym.pow_right]
  push_cast
  ring

end Work.FIArea2
