import Mathlib
import Submission.Work.MotC.constantsOnly_all

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC.C6

/-- **Two-variable rigidity.** A point of a nonsingular Weierstrass curve `W` over `L` with
coordinates in `L(u)(v) = RatFunc (RatFunc L)` descends to a point over `L`, in two steps through
`L(u) = RatFunc L`: first apply
`Work.MotC.exists_baseChange_eq_of_point_ratFunc_all` (from
`Submission.Work.MotC.constantsOnly_all`) with base field `L` and `F = RatFunc L`, then again with
`F = L`. -/
theorem exists_baseChange_eq_of_point_ratFunc2 {L : Type} [Field L] [DecidableEq L]
    [DecidableEq (RatFunc L)] [DecidableEq (RatFunc (RatFunc L))]
    (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0)
    (P : WeierstrassCurve.Affine.Point (W.baseChange (RatFunc (RatFunc L)))) :
    ∃ (Q₁ : WeierstrassCurve.Affine.Point (W.baseChange (RatFunc L)))
      (Q : WeierstrassCurve.Affine.Point (W.baseChange L)),
      WeierstrassCurve.Affine.Point.baseChange (W' := W) (RatFunc L) (RatFunc (RatFunc L)) Q₁ = P ∧
        WeierstrassCurve.Affine.Point.baseChange (W' := W) L (RatFunc L) Q = Q₁ := by
  -- Nonsingularity is preserved by the first base change `L → L(u)`.
  have hΔ₁ : (W.baseChange (RatFunc L)).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro h
    exact hΔ (RatFunc.C_injective (by simpa [RatFunc.algebraMap_eq_C] using h))
  -- Step 1: descend from `L(u)(v)` to `L(u)`.
  obtain ⟨Q₁, hQ₁⟩ :=
    Work.MotC.exists_baseChange_eq_of_point_ratFunc_all (𝕜 := L) (F := RatFunc L) W hΔ₁ P
  -- Nonsingularity is preserved by the (trivial) base change `L → L`.
  have hΔ₀ : (W.baseChange L).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro h
    exact hΔ (by simpa using h)
  -- Step 2: descend from `L(u)` to `L`.
  obtain ⟨Q, hQ⟩ :=
    Work.MotC.exists_baseChange_eq_of_point_ratFunc_all (𝕜 := L) (F := L) W hΔ₀ Q₁
  exact ⟨Q₁, Q, hQ₁, hQ⟩

end Work.MotC.C6
