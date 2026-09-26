import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The automorphy factor of `T = [[1, 1], [0, 1]]` is trivial at every point: the second
row of `T` is `(0, 1)`, so `denom T z = 0 * z + 1 = 1`. -/
lemma denom_T (z : ℍ) :
    denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) ↑z = 1 := by
  rw [ModularGroup.denom_apply]
  simp [ModularGroup.coe_T]

/-- `E₂` is invariant under `T : z ↦ z + 1`.  This is the `γ = T` case of the slash
transformation law `E₂ ∣[2] γ = E₂ - (1 / (2 ζ(2))) • D₂(γ)` for the normalized
weight-two Eisenstein series, using `D₂ T = 0`. -/
theorem E2_T_smul (z : ℍ) : E2 (ModularGroup.T • z) = E2 z := by
  have h : E2 ∣[(2 : ℤ)] ModularGroup.T = E2 := by
    rw [EisensteinSeries.E2_slash_action, EisensteinSeries.D2_T]
    simp
  have h2 := congrFun h z
  rw [SL_slash_apply] at h2
  rw [denom_T] at h2
  simpa using h2

end Work.Modular
