import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular

set_option autoImplicit false

namespace Work.ORHughesFree.StarRegular

/-- In a `∗`-regular ring every element has a relative (Moore--Penrose) inverse.  This is the
specialisation of `exists_relativeInverse` (Berberian's proposition: von Neumann regular plus
proper involution implies `∗`-regular) to the class `IsStarRegular`. -/
theorem exists_isRelativeInverse {U : Type*} [Ring U] [StarRing U] [IsStarRegular U] (x : U) :
    ∃ y : U, IsRelativeInverse x y :=
  exists_relativeInverse (inferInstance : IsStarRegular U).proper x

end Work.ORHughesFree.StarRegular
