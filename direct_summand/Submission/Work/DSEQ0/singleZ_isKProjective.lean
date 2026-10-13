import Mathlib
import Submission.Work.DSEQ0.Model

namespace Work.DSEQ0

universe u

open scoped CategoryTheory

/-- `A[0]`, the cochain complex with `A` in degree `0`, is K-projective: it is strictly bounded
above in degree `0` and all its terms are free, hence projective.  This is the input that lets
morphisms out of `A[0]` be computed in the derived category
(`CochainComplex.IsKProjective.Qh_map_bijective`). -/
theorem singleZ_isKProjective {A : Type u} [CommRing A] :
    CochainComplex.IsKProjective (Work.DSEQ0.singleZ A) :=
  CochainComplex.isKProjective_of_projective (singleZ A) 0

end Work.DSEQ0
