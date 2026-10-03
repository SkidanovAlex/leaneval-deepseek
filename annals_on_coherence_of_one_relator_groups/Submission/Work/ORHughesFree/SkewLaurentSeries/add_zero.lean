import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

theorem add_zero {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : f + 0 = f := by
  apply Subtype.ext
  funext n
  simp

end Work.ORHughesFree.SkewLaurentSeries
