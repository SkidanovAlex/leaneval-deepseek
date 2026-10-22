import Mathlib
import Submission.Work.RESOL.Resolution

open CategoryTheory

namespace Work.RESOL

/-- The resolution `X` (defined in `Submission/Work/RESOL/Resolution.lean` from the zero-preserving
atom cover) sends zero objects to the zero complex. -/
theorem isZero_X_of_isZero {K : LightCondAb}
    (hK : CategoryTheory.Limits.IsZero K) :
    CategoryTheory.Limits.IsZero (Work.RESOL.X.obj K) := by
  -- `LR.F` is the zero-preserving cover `cov`.
  have : Work.RESOL.LR.F.PreservesZeroMorphisms := Work.RESOL.cov_preservesZeroMorphisms
  -- An object is zero iff its identity is the zero morphism.
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero] at hK
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  -- `X` sends zero morphisms to zero morphisms, because `cov` does.
  have h : X.map (𝟙 K) = 0 := by
    rw [hK]
    exact CategoryTheory.Abelian.LeftResolution.chainComplexMap_zero LR K K
  rw [X.map_id K] at h
  exact h

end Work.RESOL
