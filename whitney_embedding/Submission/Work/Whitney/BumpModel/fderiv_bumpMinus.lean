import Mathlib
import Submission.Work.Whitney.BumpModel.Defs

namespace Work.Whitney.BumpModel

open scoped Manifold ContDiff
open Set Filter Topology

open Work.Whitney

/-- The mirrored cut-off model `bumpMinus n χ ρ = mirrorFun n ∘ bumpPlus n χ ρ` has derivative
`mirrorLin n ∘ D(bumpPlus n χ ρ)`: the mirror is the linear map `mirrorLin n` (whose determinant is
`-1`), so precomposing with it multiplies the determinant of the "two sheets" endomorphism by `-1`
and hence flips the sign of the double point. -/
theorem fderiv_bumpMinus (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ} {ρ : ℝ}
    (h : ContDiff ℝ ∞ (bumpPlus n χ ρ)) (x : Fin n → ℝ) :
    (fderiv ℝ (bumpMinus n χ ρ) x).toLinearMap
      = (mirrorLin n) ∘ₗ (fderiv ℝ (bumpPlus n χ ρ) x).toLinearMap := by
  -- `mirrorFun n` is the continuous linear map attached to the linear map `mirrorLin n`.
  have hfun : mirrorFun n = ⇑(LinearMap.toContinuousLinearMap (mirrorLin n)) := by
    funext y
    change mirrorFun n y = mirrorLin n y
    exact (mirrorLin_apply n y).symm
  -- `bumpMinus` is by definition the mirror of `bumpPlus`.
  have hmin : bumpMinus n χ ρ = mirrorFun n ∘ bumpPlus n χ ρ := rfl
  have hdiff : DifferentiableAt ℝ (bumpPlus n χ ρ) x :=
    (h.differentiable (by simp)).differentiableAt
  have hMdiff : DifferentiableAt ℝ (mirrorFun n) (bumpPlus n χ ρ x) := by
    rw [hfun]; exact (LinearMap.toContinuousLinearMap (mirrorLin n)).differentiableAt
  -- Chain rule, then the derivative of a continuous linear map is itself.
  rw [hmin, fderiv_comp (𝕜 := ℝ) x hMdiff hdiff]
  rw [show fderiv ℝ (mirrorFun n) (bumpPlus n χ ρ x)
        = LinearMap.toContinuousLinearMap (mirrorLin n) from by
      rw [hfun]; exact ContinuousLinearMap.fderiv _]
  -- Pass from continuous linear maps back to linear maps.
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.coe_toContinuousLinearMap]

end Work.Whitney.BumpModel
