import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The null ray over `y` agrees with `y` on the first four coordinates. -/
theorem ray_castSucc (y : E4) (i : Fin 4) : ray y i.castSucc = y i := by
  fin_cases i <;> simp [ray]

/-- The Klein lift `y ↦ (y,1)/√(1−|y|²)` is injective on the open unit ball: it is the
hyperboloid-coordinate incarnation of the affine chart `x₄ = 1`, and on the ball its last
coordinate `(√(1−|y|²))⁻¹` is a nonzero scalar, so equality of the lifts forces equality of the
underlying points of the ball. -/
theorem hypOfKlein_injOn : Set.InjOn hypOfKlein ball := by
  intro x hx y hy hxy
  have hx1 : ‖x‖ < 1 := hx
  have hxpos : 0 < 1 - ‖x‖ ^ 2 := by
    have h2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
    linarith
  have hc : (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hxpos))
  -- the common value of the last coordinate is the scalar `(√(1−|·|²))⁻¹`
  have h4 : (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹ = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ := by
    have h := congrFun hxy (4 : Fin 5)
    simpa using h
  refine PiLp.ext (fun i => ?_)
  have key : (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹ * x i = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * y i := by
    have h := congrFun hxy (i.castSucc)
    have h1 : ray x i.castSucc = x i := ray_castSucc x i
    have h2 : ray y i.castSucc = y i := ray_castSucc y i
    simpa [hypOfKlein, h1, h2] using h
  rw [← h4] at key
  exact mul_left_cancel₀ hc key

end Work.HypModel
