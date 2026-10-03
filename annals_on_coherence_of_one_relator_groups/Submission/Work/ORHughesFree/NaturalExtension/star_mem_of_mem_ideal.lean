import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.exists_isRelativeInverse

namespace Work.ORHughesFree.NaturalExtension

/-- In a `∗`-regular ring every two-sided ideal is closed under `star`.

Indeed, let `x ∈ I` and let `y` be a relative (Moore--Penrose) inverse of `x`, so that
`x * y` is a projection with `x = (x * y) * x`.  Since `I` is two-sided, `x * y ∈ I`, and
`star x = star (x * y * x) = star x * star (x * y) = star x * (x * y) ∈ I`, because
`x * y` is self-adjoint and `I` is a left ideal. -/
theorem star_mem_of_mem_ideal {R : Type} [Ring R] [StarRing R] [IsStarRegular R] (I : Ideal R) [I.IsTwoSided] {x : R}
    (h : x ∈ I) : star x ∈ I := by
  obtain ⟨y, hy⟩ := Work.ORHughesFree.StarRegular.exists_isRelativeInverse x
  have hI : x * y ∈ I := I.mul_mem_right y h
  have h1 : star ((x * y) * x) = star x := by rw [hy.left]
  rw [star_mul, hy.star_left] at h1
  rw [← h1]
  exact I.mul_mem_left (star x) hI

end Work.ORHughesFree.NaturalExtension
