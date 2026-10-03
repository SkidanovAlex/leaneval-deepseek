import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

theorem add_assoc {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g h : SkewLaurentSeries A) : f + g + h = f + (g + h) := by
  apply Subtype.ext
  funext n
  exact _root_.add_assoc (f.1 n) (g.1 n) (h.1 n)

end Work.ORHughesFree.SkewLaurentSeries
