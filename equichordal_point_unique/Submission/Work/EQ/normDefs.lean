import Mathlib
import Submission.Work.EQ.Defs

/-! Auxiliary definitions for the normalisation lemma `Work.EQ.exists_normEqCurve`. -/

namespace Work.EQ

open LeanEval.Geometry.Equichordal

/-- `K - O`, the translate of `K` carrying `O` to the origin. -/
noncomputable def shiftSet (K : Set Plane) (O : Plane) : Set Plane :=
  (Homeomorph.addLeft (-O)) '' K

/-- The radial function of `K` about the (interior) point `O`: the distance from `O` to the
frontier of `K` along the direction `v`, i.e. `1 / gauge (K - O) v`. -/
noncomputable def radFn (K : Set Plane) (O : Plane) (v : Plane) : ℝ :=
  (gauge (shiftSet K O) v)⁻¹

/-- The plane `EuclideanSpace ℝ (Fin 2)` identified with `ℂ` by `x ↦ x 0 + x 1 * I`. -/
noncomputable def toC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

end Work.EQ
