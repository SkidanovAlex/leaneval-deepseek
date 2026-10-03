import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The number of Gaussian integers of norm `n`.  For `n > 0` this is the classical `r₂(n)`,
i.e. the number of pairs `(a,b) ∈ ℤ²` with `a² + b² = n` (the box restriction `|a|,|b| ≤ n` is
harmless since `a² ≤ n` forces `|a| ≤ n`; see `r2count_eq_pair_count`).

Here `gnorm z = z.norm.natAbs = |z|²`. -/
def r2count (n : ℕ) : ℕ :=
  ((Work.FIPlan.gBox (n : ℤ)).filter (fun w => Work.FIPlan.gnorm w = n)).card

/-- The same count as `r2count`, written with integer pairs `(a,b)`: the number of `(a,b)` with
`a² + b² = n`. -/
def r2pair (n : ℕ) : ℕ :=
  (((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
    (fun q : ℤ × ℤ => q.1 ^ 2 + q.2 ^ 2 = (n : ℤ))).card

/-- The multiplicative weight `G(s) = ∏_{p ∣ s, p ≡ 1 (4)} (2·v_p(s) + 1)` of the a-count bound. -/
noncomputable def Gwt (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors.filter (fun p => p % 4 = 1), ((2 * s.factorization p + 1 : ℕ) : ℝ)

end

end Work.FIArea7
