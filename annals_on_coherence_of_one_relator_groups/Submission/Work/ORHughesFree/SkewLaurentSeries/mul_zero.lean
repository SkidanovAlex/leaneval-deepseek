import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Right multiplication by `0` in `A((t;τ))` is zero.

Indeed, the `n`-th coefficient of `f * 0` is
`∑ k ∈ [lo f, n - lo 0], f k * (k • (0 : A))`, and every summand is `0`. -/
theorem mul_zero {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : f * 0 = 0 := by
  apply Subtype.ext
  funext n
  rw [mul_apply]
  simp

end Work.ORHughesFree.SkewLaurentSeries
