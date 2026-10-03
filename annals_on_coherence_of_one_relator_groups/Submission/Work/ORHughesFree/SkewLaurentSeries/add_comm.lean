import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

theorem add_comm {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g : SkewLaurentSeries A) : f + g = g + f := by
  apply Subtype.ext
  funext n
  exact _root_.add_comm (f.1 n) (g.1 n)

end Work.ORHughesFree.SkewLaurentSeries
