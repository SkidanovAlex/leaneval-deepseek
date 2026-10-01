/-
# `λ(p ^ k)` for a prime power

For `λ(n) = Σ_{d | n} χ(d)` (see `Work.LinnikAreas.lam`), the divisors of a prime power `p ^ k`
are exactly `1, p, p^2, …, p^k`, so

  `λ(p ^ k) = Σ_{j = 0}^{k} χ(p ^ j) = Σ_{j = 0}^{k} χ(p)^j`.

The right-hand side is the value at `k` of a finite geometric sum, which is how `λ(p ^ k)` is
resummed in the Euler-product bookkeeping for `ζ(s)L(s,χ)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

/-- `λ` evaluated at a prime power: `λ(p ^ k) = Σ_{j ≤ k} χ(p)^j`.

Since the divisors of `p ^ k` are `p ^ j` for `0 ≤ j ≤ k` and `χ` is multiplicative with
`χ(1) = 1`, this is the geometric sum of the values of `χ` at powers of `p`. -/
theorem lamPrimePow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {p k : ℕ} (hp : p.Prime) :
    Work.LinnikAreas.lam χ (p ^ k) = ∑ j ∈ Finset.range (k + 1), (χ (p : ZMod q)) ^ j := by
  rw [lam, Nat.sum_divisors_prime_pow hp]
  simp [Nat.cast_pow]

end Work.LinnikAreas
