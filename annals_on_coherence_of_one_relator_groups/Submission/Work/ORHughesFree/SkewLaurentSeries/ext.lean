import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

theorem ext {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {f g : SkewLaurentSeries A} (h : ∀ n : ℤ, f.1 n = g.1 n) : f = g :=
  Subtype.ext (funext h)

end Work.ORHughesFree.SkewLaurentSeries
