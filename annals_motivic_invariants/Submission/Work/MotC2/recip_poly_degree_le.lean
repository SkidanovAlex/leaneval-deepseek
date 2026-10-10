import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotC2

/--
If `A : L[X]` has degree at most `n` and `x : K` is a nonzero element of an `L`-algebra `K`,
then there is a polynomial `B : L[X]` of degree at most `n` whose value at `x` is
`x ^ n * A (x⁻¹)`.

The witness is the reversed polynomial `A.reflect n`: reading the coefficients of `A`
backwards, `B = ∑ i, A.coeff i • X ^ (n - i)`, so that
`B(x) = ∑ i, A.coeff i * x ^ (n - i) = x ^ n * ∑ i, A.coeff i * (x⁻¹) ^ i = x ^ n * A(x⁻¹)`.
-/
theorem recip_poly_degree_le {L K : Type*} [Field L] [Field K] [Algebra L K]
    (x : K) (hx : x ≠ 0) (A : Polynomial L) (n : ℕ) (hn : A.natDegree ≤ n) :
    ∃ B : Polynomial L, B.natDegree ≤ n ∧
      Polynomial.aeval x B = x ^ n * Polynomial.aeval (x⁻¹) A := by
  refine ⟨A.reflect n, ?_, ?_⟩
  · -- the reversed polynomial has degree at most `n`
    simpa [Nat.max_eq_left hn] using (Polynomial.natDegree_reflect_le (p := A) (N := n))
  · haveI : Invertible x := invertibleOfNonzero hx
    -- `reflect n` interacts with evaluation by `(reflect n A)(x⁻¹) * x ^ n = A(x)`;
    -- applying it to `A.reflect n` (whose `reflect n` is `A` again) gives the claim.
    have h := Polynomial.eval₂_reflect_mul_pow (algebraMap L K) x n (A.reflect n)
      (by simpa [Nat.max_eq_left hn] using (Polynomial.natDegree_reflect_le (p := A) (N := n)))
    rw [Polynomial.reflect_reflect, invOf_eq_inv] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← h, mul_comm]

end Work.MotC2
