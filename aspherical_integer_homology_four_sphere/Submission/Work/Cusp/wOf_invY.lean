import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `wOf` is a left inverse of `invY`

`wOf v` and `invY v` are the two halves of the `2 × 2` linear system relating the torus
coordinates `y = (y₂,y₃)` of the cusp `v` to the orthonormal `σ_v^⊥`-coordinates
`w = (⟪y₂λ₂ + y₃λ₃, frame2 v⟫, ⟪y₂λ₂ + y₃λ₃, frame3 v⟫)`:  `wOf v` is the matrix
`G = (⟪λ_i, frame_j⟫)` itself, and `invY v` is the adjugate over the determinant,

  `invY v w = wDet v⁻¹ • (g₁₁w₀ − g₀₁w₁, −g₁₀w₀ + g₀₀w₁)`.

So `wOf v (invY v w) = w` is the statement that `G · G⁻¹ = 1`, and it is exactly the
non-vanishing of `wDet v` (= `det G`) that makes it true: `invY v` is *not* a two-sided inverse
of `wOf v` without it, since `(0)⁻¹ = 0`.

The determinant is nonzero because `(σ_v, κ_{v,2}, κ_{v,3})` is a basis of `ℝ³`: it is a concrete
computation on the data tables `Data.kappa`/`Data.slopeB`, carried out below.
-/

open scoped Real InnerProductSpace

namespace Work.Cusp

/-- The determinant `wDet v` of the `w`-matrix is nonzero, proved directly from the data tables
(`Data.kappa`, `Data.slopeB`): for each of the five cusps the matrix `G = (⟪λ_i, frame_j⟫)` is
explicit and its determinant evaluates to a nonzero rational number. -/
theorem wDet_ne_zero_aux (v : Fin 5) : wDet v ≠ 0 := by
  fin_cases v <;>
    simp [wDet, frame2, frame3, frame2aux, lam2, lam3, kv, kappa, slope, slopeB, slopeC,
      PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.norm_eq]
  all_goals (constructor <;> · (rw [Real.sq_sqrt (by positivity)]; norm_num))

/-- **`wOf v` is a left inverse of `invY v`**: the adjugate formula of `invY v` really inverts the
`w`-matrix `wOf v`.  Componentwise this is the polynomial identity
`d⁻¹(g₁₁w₀ − g₀₁w₁)g₀₀ + d⁻¹(−g₁₀w₀ + g₀₀w₁)g₀₁ = w₀` (and its analogue in the second
component), where `d = g₀₀g₁₁ − g₀₁g₁₀ = wDet v ≠ 0`. -/
theorem wOf_invY (v : Fin 5) (w : E2) : wOf v (invY v w) = w := by
  have hd : ⟪lam2 v, frame2 v⟫_ℝ * ⟪lam3 v, frame3 v⟫_ℝ
      - ⟪lam3 v, frame2 v⟫_ℝ * ⟪lam2 v, frame3 v⟫_ℝ ≠ 0 := wDet_ne_zero_aux v
  ext i
  fin_cases i <;> simp [wOf, invY, cuspY, inner_add_left, real_inner_smul_left]
  all_goals (field_simp; ring)

end Work.Cusp
