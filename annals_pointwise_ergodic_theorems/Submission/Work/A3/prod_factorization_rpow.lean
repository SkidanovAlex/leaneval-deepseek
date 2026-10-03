import Mathlib
import Submission.Work.A3.Circle

namespace Work.A3

/-- The real-valued product `∏_{p | q} (p ^ v_p(q)) ^ (1-η)` equals `q ^ (1-η)`.

Indeed `∏_{p | q} p ^ v_p(q) = q` (`Nat.prod_factorization_pow_eq_self`), and the
`(1-η)`-th power of a product of nonnegative reals is the product of the
`(1-η)`-th powers (`Real.finsetProd_rpow`). -/
theorem prod_factorization_rpow (q : ℕ) (hq : 1 ≤ q) (η : ℝ) :
    (∏ p ∈ q.primeFactors, ((p ^ q.factorization p : ℕ) : ℝ) ^ (1 - η))
      = (q : ℝ) ^ (1 - η) := by
  have hq0 : q ≠ 0 := by omega
  -- the underlying natural-number factorization identity, pushed through the cast
  have hnat : ∏ p ∈ q.primeFactors, ((p ^ q.factorization p : ℕ) : ℝ) = (q : ℝ) := by
    rw [← Nat.cast_prod,
      show (∏ p ∈ q.primeFactors, p ^ q.factorization p) = q from ?_]
    rw [← Nat.support_factorization]
    exact Nat.prod_factorization_pow_eq_self hq0
  -- `(∏ f) ^ r = ∏ f ^ r` for nonnegative factors
  rw [Real.finsetProd_rpow q.primeFactors _ (fun p _ => by positivity) (1 - η), hnat]

end Work.A3
