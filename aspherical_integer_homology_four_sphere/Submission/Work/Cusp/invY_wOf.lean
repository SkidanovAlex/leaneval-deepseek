import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The determinant `wDet v = g00·g11 − g01·g10` of the `w`-matrix
`G = (⟪λ_i, e_j⟫)` is nonzero, so that `invY` is an honest inverse of the map `wOf`.
Here `(κ_{v,1}, κ_{v,2}, κ_{v,3})` is an orthogonal `ℤ`-basis of the cusp lattice `Λ_v`
and `σ_v = κ_{v,1} + b_v κ_{v,2}` lies in the `κ₁κ₂`-plane, so `frame2` lies in that plane
while `frame3 ∥ κ_{v,3}`; the cases of `Data.kappa` give the value explicitly. -/
private theorem wDet_ne_zero_aux (v : Fin 5) : wDet v ≠ 0 := by
  fin_cases v <;>
    simp [wDet, frame2, frame2aux, frame3, lam2, lam3, slope, kv, kappa, slopeB, slopeC,
          PiLp.inner_apply, Fin.sum_univ_three, PiLp.norm_eq_of_L2] <;>
    rw [Real.sq_sqrt (by norm_num)] <;> norm_num

/-- `wOf` in components: `wOf v y` is `G y` for the matrix `G = (⟪λ_i, e_j⟫)`. -/
private theorem wOf_apply_zero (v : Fin 5) (y : E2) :
    wOf v y 0 = ⟪lam2 v, frame2 v⟫_ℝ * y 0 + ⟪lam3 v, frame2 v⟫_ℝ * y 1 := by
  simp [wOf, cuspY, real_inner_smul_left, inner_add_left]
  ring

/-- `wOf` in components, second coordinate. -/
private theorem wOf_apply_one (v : Fin 5) (y : E2) :
    wOf v y 1 = ⟪lam2 v, frame3 v⟫_ℝ * y 0 + ⟪lam3 v, frame3 v⟫_ℝ * y 1 := by
  simp [wOf, cuspY, real_inner_smul_left, inner_add_left]
  ring

/-- `invY` is a left inverse of `wOf`: it inverts the `2 × 2` system `w = G y`, the determinant
`wDet v` being nonzero (`wDet_ne_zero_aux`). -/
theorem invY_wOf (v : Fin 5) (y : E2) : invY v (wOf v y) = y := by
  have hdet : ⟪lam2 v, frame2 v⟫_ℝ * ⟪lam3 v, frame3 v⟫_ℝ
      - ⟪lam3 v, frame2 v⟫_ℝ * ⟪lam2 v, frame3 v⟫_ℝ ≠ 0 := wDet_ne_zero_aux v
  have hw0 := wOf_apply_zero v y
  have hw1 := wOf_apply_one v y
  ext i
  fin_cases i
  · simp [invY, hw0, hw1]
    field_simp
    ring
  · simp [invY, hw0, hw1]
    field_simp
    ring

end Work.Cusp
