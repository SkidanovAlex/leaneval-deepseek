import Mathlib
import Submission.Work.Drive.LensSpaceGlue

namespace Work.Drive

/-- **The `S¹`-coordinate of a linear interpolation has a smooth halving.**  For a class
`Θ + u ∈ ℝ/ℤ` and a square root `w₀` of `circleOf (Θ + u)` (unit norm), the class of
`Θ + s * δ` (`s, δ : ℝ`) is the square of the unit complex number
`w₀ * circleOf (s * δ / 2)`: the halving of the interpolated class is obtained by interpolating the
halved *real* angle.

This is the algebraic core of the statement that the cone `Work.Drive.capConePt`
(`(s,t) ↦ ((1-s) r₀ + s ρ t, ⟦Θ 0 + s (Θ t - Θ 0)⟧ + u, s · circleOf (Ψ t))`) has a smooth sphere
lift: with `Θ := Θ 0`, `δ := Θ t - Θ 0` the cone's `S¹`-coordinate is `circOf (z ^ 2)` for the
smooth `z := w₀ * circleOf (s * (Θ t - Θ 0) / 2)`, so the cone can be fed to
`Work.Drive.lensToProj_capTorus` (`lensToProj ⟦inl (θ, d)⟧ = mk ℝ (capProjVecOf z d) ⋯` for
`z ^ 2 = circleOf θ`) and hence to `Work.Drive.contMDiffAt_cappingSpace_capPiece`; see
`Submission/Work/Drive/CAPPING_ANALYSIS.md` §2 and
`Submission/Work/Drive/SMOOTHNESS_LANE_STATUS.md`.  The square root is unavoidable here (there is no
continuous choice of `w₀` as a function of the class), which is why the halving is carried as data.

Route: `w₀ ^ 2 * (circleOf (s * δ / 2)) ^ 2 = circleOf (Θ + u) * circleOf (s * δ / 2 + s * δ / 2)`
(by `circleOf_add`, using `‖w₀‖ = 1`), and `circleOf (Θ + u) * circleOf (s * δ) =
circleOf (Θ + u + s * δ)` (`circleOf_add`), whence `circOf` of both sides agrees
(`Work.Drive.circleOf_circOf`, `Work.Drive.circOf` and `AddCircle.coe_add`); `circleOf_injective`
turns the equality of `circleOf`-images into the required equality of classes. -/
theorem circOf_half_sq (Θ : ℝ) (u : UnitAddCircle) {w₀ : ℂ}
    (hw : w₀ ^ 2 = circleOf (((Θ : ℝ) : UnitAddCircle) + u)) (hw1 : ‖w₀‖ = 1) (s δ : ℝ) :
    Work.Drive.circOf ((w₀ * circleOf (((s * δ / 2 : ℝ)) : UnitAddCircle)) ^ 2)
        (by rw [norm_pow, norm_mul, hw1, norm_circleOf, mul_one, one_pow])
      = (((Θ + s * δ : ℝ)) : UnitAddCircle) + u := by
  apply circleOf_injective
  rw [circleOf_circOf]
  -- the halved angle class is the square root of the full angle class
  have hsq : circleOf (((s * δ / 2 : ℝ)) : UnitAddCircle) ^ 2
      = circleOf (((s * δ : ℝ)) : UnitAddCircle) := by
    rw [← circleOf_nsmul 2]
    congr 1
    rw [two_nsmul, ← AddCircle.coe_add]
    norm_num
  rw [mul_pow, hsq, hw, AddCircle.coe_add, circleOf_add, circleOf_add, circleOf_add]
  ring

end Work.Drive
