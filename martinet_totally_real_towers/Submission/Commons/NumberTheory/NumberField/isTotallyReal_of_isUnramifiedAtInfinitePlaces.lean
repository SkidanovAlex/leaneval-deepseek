import Mathlib
import Submission.Commons.NumberTheory.NumberField.totallyReal_of_unramifiedAtInfinitePlaces
import Submission.Commons.NumberTheory.NumberField.nrComplexPlaces_mul_finrank_of_galois

namespace Commons.NumberTheory.NumberField

/-- **An extension of a totally real number field that is unramified at all infinite places
is again totally real.**

Every infinite place `w` of `K` is unramified over `k`
(`NumberField.InfinitePlace.isUnramified`); by
`NumberField.InfinitePlace.isUnramified_iff` and `not_isComplex_iff_isReal` this means `w` is
real as soon as `w.comap (algebraMap k K)` is real, which holds because `k` is totally real. -/
theorem isTotallyReal_of_isUnramifiedAtInfinitePlaces (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [NumberField.IsTotallyReal k] [IsUnramifiedAtInfinitePlaces k K] : NumberField.IsTotallyReal K :=
  totallyReal_of_unramifiedAtInfinitePlaces k K (inferInstanceAs (NumberField.IsTotallyReal k))

end Commons.NumberTheory.NumberField
