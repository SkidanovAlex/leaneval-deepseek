import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

theorem zero_add {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : 0 + f = f := by
  apply Subtype.ext
  funext n
  simp

end Work.ORHughesFree.SkewLaurentSeries
