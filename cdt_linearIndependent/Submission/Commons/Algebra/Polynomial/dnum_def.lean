import Mathlib.Algebra.Polynomial.Derivative
import Submission.Commons.Algebra.WeylOps.starMul_def

namespace Commons.Algebra.Polynomial

/-- The falling factorial `(N)_j = N (N−1) ⋯ (N−j+1)` in `ℤ`. -/
def fallFact (N : ℤ) (j : ℕ) : ℤ := (Finset.range j).prod (fun i => N - (i : ℤ))

/-- The numerator of the `j`-th derivative of the quotient `p/q`:
`(p/q)^{(j)} = C_j / q^{j+1}`. -/
noncomputable def dnum {K : Type*} [Field K] (p q : Polynomial K) : ℕ → Polynomial K
  | 0 => p
  | (j + 1) => (dnum p q j).derivative * q
      - Polynomial.C (((j : ℕ) + 1 : ℕ) : K) * (dnum p q j * q.derivative)

/-- Unfolding formula for `dnum` at a successor. -/
theorem dnum_def {K : Type*} [Field K] (p q : Polynomial K) (j : ℕ) :
    dnum p q (j + 1) = (dnum p q j).derivative * q
      - Polynomial.C (((j : ℕ) + 1 : ℕ) : K) * (dnum p q j * q.derivative) := by
  rfl

end Commons.Algebra.Polynomial