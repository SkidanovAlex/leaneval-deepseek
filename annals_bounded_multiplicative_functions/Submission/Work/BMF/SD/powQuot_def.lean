import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integer `((n+q)^j - n^j)/q`

For naturals `n, q, j` the number `(n+q)^j - n^j` is divisible by `q`, and this file
introduces an *explicit* integral representative of the quotient,

`powQuot n q j = ∑ i ∈ range j, (n+q)^i * n^(j-1-i)`,

together with the elementary fact that it is non-negative.  Both facts are used by
`Work.BMF.SD.a_one_bound_perturb`.
-/

namespace Work.BMF.SD

/-- The integer `((n+q)^j - n^j)/q`, written as the explicit polynomial
`∑_{i<j} (n+q)^i n^{j-1-i}` in `ℤ`. -/
def powQuot (n q j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range j, (n + q : ℤ) ^ i * (n : ℤ) ^ (j - 1 - i)

lemma powQuot_nonneg (n q j : ℕ) : 0 ≤ powQuot n q j := by
  rw [powQuot]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)

end Work.BMF.SD
