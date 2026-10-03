import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Every nonzero skew Laurent series has a least index at which its coefficient is nonzero: the
support of `f` is nonempty (as `f ≠ 0`) and bounded below (by the vanishing bound in the
definition of `SkewLaurentSeries`), and `ℤ` is well-ordered below. -/
theorem exists_least_nonzero_coeff {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A] (f : SkewLaurentSeries A) (hf : f ≠ 0) : ∃ m : ℤ, f.1 m ≠ 0 ∧ ∀ n : ℤ, n < m → f.1 n = 0 := by
  obtain ⟨N, hN⟩ := f.2
  -- the support is nonempty, since `f` is not the zero series
  have hne : ∃ n : ℤ, f.1 n ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext fun n => h n))
  -- and bounded below by `N`
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd
    (P := fun n : ℤ => f.1 n ≠ 0)
    ⟨N, fun z hz => by
      by_contra hzN
      exact hz (hN z (by omega))⟩
    hne
  exact ⟨m, hm, fun n hn => by
    by_contra h
    exact absurd (hmin n h) (not_le.mpr hn)⟩

end Work.ORHughesFree.SkewLaurentSeries
