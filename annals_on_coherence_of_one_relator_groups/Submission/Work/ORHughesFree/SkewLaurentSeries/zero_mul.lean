import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Left multiplication by `0` in `A((t;τ))` is zero.

Indeed, the `n`-th coefficient of `0 * f` is
`∑ k ∈ [lo 0, n - lo f], (0 : A) * (k • f (n - k))`, and every summand is `0`. -/
theorem zero_mul {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : 0 * f = 0 := by
  apply Subtype.ext
  funext n
  rw [mul_apply]
  simp

end Work.ORHughesFree.SkewLaurentSeries
