import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds
import Submission.Work.ORHughesFree.SkewLaurentSeries.ext
import Submission.Work.ORHughesFree.SkewLaurentSeries.t_mul_apply
import Submission.Work.ORHughesFree.SkewLaurentSeries.coeff_mul_apply

namespace Work.ORHughesFree.SkewLaurentSeries

/-- The commutation relation `t a = τ(a) t` defining the skew Laurent series ring `A((t;τ))`:
multiplying the central variable `t` into a coefficient `a` on the left moves `a` past `t` at the
cost of applying `τ = ofAdd 1` to it.

Both sides are computed coefficientwise at `n : ℤ`.  By `t_mul_apply` the left-hand side has
`n`-th coefficient `τ ((coeff a) n) = if n = 1 then τ a else 0`, while by `coeff_mul_apply` the
right-hand side has `n`-th coefficient `τ a * t_n = if n = 1 then τ a else 0`. -/
theorem t_mul_coeff {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] (a : A) :
    (t : SkewLaurentSeries A) * coeff a =
      coeff ((Multiplicative.ofAdd (1 : ℤ)) • a) * t := by
  apply ext
  intro n
  rw [t_mul_apply, coeff_mul_apply, coeff_apply, t_apply]
  by_cases h : n = 1
  · subst h
    simp
  · have h1 : n - 1 ≠ 0 := by omega
    simp [h, h1]

end Work.ORHughesFree.SkewLaurentSeries
