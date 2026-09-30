import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The Euclidean dot product on `V5 = ℝ⁵` splits as the dot product of the first four
coordinates plus the product of the last coordinates. -/
theorem dotProduct_five_eq (u v : V5) :
    u ⬝ᵥ v = (proj4 u ⬝ᵥ proj4 v) + u 4 * v 4 := by
  simp only [dotProduct, proj4, Fin.sum_univ_five, Fin.sum_univ_four]
  simp

/-- The Euclidean dot product of two points of the upper sheet of the hyperboloid is positive.
Indeed, writing `a = proj4 u`, `b = proj4 v`, the Lorentz condition `⟨u,u⟩ = -1` reads
`‖a‖² = u₄² - 1 < u₄²`, so `‖a‖ < u₄` (and likewise `‖b‖ < v₄`); Cauchy–Schwarz then gives
`u ⬝ᵥ v = ⟪a,b⟫ + u₄v₄ ≥ -‖a‖‖b‖ + u₄v₄ > 0`. -/
theorem dotProduct_pos_of_upperSheet {u v : V5} (hu : u ∈ upperSheet) (hv : v ∈ upperSheet) :
    0 < u ⬝ᵥ v := by
  have hdot : u ⬝ᵥ v = (proj4 u ⬝ᵥ proj4 v) + u 4 * v 4 := dotProduct_five_eq u v
  have hu4 : 0 < u 4 := hu.2
  have hv4 : 0 < v 4 := hv.2
  have hnorm_u : ‖proj4 u‖ ^ 2 = (u 4) ^ 2 - 1 := by
    have h1 : lorentz u u = (proj4 u ⬝ᵥ proj4 u) - u 4 * u 4 := lorentz_eq_dotProduct_proj4 u u
    have h2 : proj4 u ⬝ᵥ proj4 u = ⟪proj4 u, proj4 u⟫_ℝ := (inner_eq_dotProduct _ _).symm
    have h3 : ⟪proj4 u, proj4 u⟫_ℝ = ‖proj4 u‖ ^ 2 := real_inner_self_eq_norm_sq _
    have h4 : lorentz u u = -1 := hu.1
    rw [h4] at h1
    nlinarith [h1, h2, h3]
  have hnorm_v : ‖proj4 v‖ ^ 2 = (v 4) ^ 2 - 1 := by
    have h1 : lorentz v v = (proj4 v ⬝ᵥ proj4 v) - v 4 * v 4 := lorentz_eq_dotProduct_proj4 v v
    have h2 : proj4 v ⬝ᵥ proj4 v = ⟪proj4 v, proj4 v⟫_ℝ := (inner_eq_dotProduct _ _).symm
    have h3 : ⟪proj4 v, proj4 v⟫_ℝ = ‖proj4 v‖ ^ 2 := real_inner_self_eq_norm_sq _
    have h4 : lorentz v v = -1 := hv.1
    rw [h4] at h1
    nlinarith [h1, h2, h3]
  have hlt_u : ‖proj4 u‖ < u 4 := by
    have h : ‖proj4 u‖ ^ 2 < (u 4) ^ 2 := by nlinarith [hnorm_u]
    have := (sq_lt_sq.mp h)
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hu4] at this
  have hlt_v : ‖proj4 v‖ < v 4 := by
    have h : ‖proj4 v‖ ^ 2 < (v 4) ^ 2 := by nlinarith [hnorm_v]
    have := (sq_lt_sq.mp h)
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hv4] at this
  have hcs : -(‖proj4 u‖ * ‖proj4 v‖) ≤ ⟪proj4 u, proj4 v⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hprod : ‖proj4 u‖ * ‖proj4 v‖ < u 4 * v 4 := by
    nlinarith [hlt_u, hlt_v, norm_nonneg (proj4 u), norm_nonneg (proj4 v), hu4, hv4]
  have hinner : (proj4 u ⬝ᵥ proj4 v) = ⟪proj4 u, proj4 v⟫_ℝ := inner_eq_dotProduct _ _
  rw [hdot, hinner]
  linarith

end Work.HypModel
