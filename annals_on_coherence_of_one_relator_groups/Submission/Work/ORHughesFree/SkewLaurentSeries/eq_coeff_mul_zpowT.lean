import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.Prop51.coeff_zpowT

namespace Work.ORHughesFree.SkewLaurentSeries

theorem eq_coeff_mul_zpowT {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f : Work.ORHughesFree.SkewLaurentSeries A) (k : ℤ)
    (h : ∀ j : ℤ, j ≠ k → f.1 j = 0) :
    f = Work.ORHughesFree.skewLaurentCoeff A (f.1 k) *
      ↑((Work.ORHughesFree.skewLaurentSeriesT A) ^ k) := by
  apply Subtype.ext
  funext m
  rw [Work.ORHughesFree.Prop51.coeff_zpowT]
  by_cases hm : m = k
  · rw [if_pos hm, hm]
  · rw [if_neg hm, h m hm]

end Work.ORHughesFree.SkewLaurentSeries
