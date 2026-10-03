import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

theorem neg_add_cancel {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : SkewLaurentSeries A) : -f + f = 0 := by
  apply Subtype.ext
  funext n
  simp

end Work.ORHughesFree.SkewLaurentSeries
