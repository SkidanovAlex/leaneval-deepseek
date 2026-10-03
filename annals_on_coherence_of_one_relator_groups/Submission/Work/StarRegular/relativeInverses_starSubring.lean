import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.isRelativeInverse_unique
import Submission.Work.ORHughesFree.StarRegular.exists_isRelativeInverse
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_le

namespace Work.StarRegular

theorem relativeInverses_starSubring {U : Type*} [Ring U] [StarRing U] (A : Work.ORHughesFree.StarSubring U)
    [Work.ORHughesFree.IsStarRegular ↥A] :
    Work.ORHughesFree.relativeInverses (A : Set U) ⊆ (A : Set U) := by
  rintro y ⟨x, hx, hrel⟩
  -- `x ∈ A` and `A` is `∗`-regular, so `x` has a relative inverse `z` inside `A`.
  obtain ⟨z, hz⟩ := Work.ORHughesFree.StarRegular.exists_isRelativeInverse (U := ↥A) ⟨x, hx⟩
  -- Lift that relative inverse to the ambient ring `U`.
  have hz' : Work.ORHughesFree.IsRelativeInverse x ((z : U)) :=
    Work.ORHughesFree.StarRegular.isRelativeInverse_lift A hz
  -- Relative inverses are unique in any `∗`-ring, so `y` is that element of `A`.
  have hy : y = ((z : U)) :=
    Work.ORHughesFree.StarRegular.isRelativeInverse_unique hrel hz'
  rw [hy]
  exact z.2

end Work.StarRegular
