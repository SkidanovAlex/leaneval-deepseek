import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Matrix InnerProductSpace

namespace Work.HypModel

/-- The squared Euclidean norm of `proj4 u` is the sum of the squares of the first four
coordinates of `u`. -/
private theorem proj4_norm_sq (u : V5) :
    ‖proj4 u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
  simp [proj4, dotProduct, Fin.sum_univ_four]
  ring

/-- **The Lorentz form is negative on pairs of points of the upper sheet of the hyperboloid.**
This is the reverse Cauchy–Schwarz inequality for two timelike vectors of the same time
orientation. -/
theorem lorentz_neg_of_upperSheet {u v : V5} (hu : u ∈ upperSheet) (hv : v ∈ upperSheet) :
    lorentz u v < 0 := by
  obtain ⟨hu1, hu4⟩ := hu
  obtain ⟨hv1, hv4⟩ := hv
  -- the Lorentz square of `u` in coordinates
  have hu1' : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 + u 3 * u 3 - u 4 * u 4 = -1 := by
    simpa using hu1
  have hv1' : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 + v 3 * v 3 - v 4 * v 4 = -1 := by
    simpa using hv1
  -- the norm of the spatial part of `u` (and of `v`)
  have hPu : ‖proj4 u‖ ^ 2 = u 4 ^ 2 - 1 := by
    rw [proj4_norm_sq]
    nlinarith [hu1', sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
  have hQv : ‖proj4 v‖ ^ 2 = v 4 ^ 2 - 1 := by
    rw [proj4_norm_sq]
    nlinarith [hv1', sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hA : 0 ≤ u 4 ^ 2 - 1 := by rw [← hPu]; positivity
  have hB : 0 ≤ v 4 ^ 2 - 1 := by rw [← hQv]; positivity
  -- hence the two positive timelike coordinates are at least `1`
  have hx : 1 ≤ u 4 ^ 2 := by linarith
  have hy : 1 ≤ v 4 ^ 2 := by linarith
  -- the Cauchy–Schwarz bound
  have hcs : ⟪proj4 u, proj4 v⟫_ℝ ≤ ‖proj4 u‖ * ‖proj4 v‖ := real_inner_le_norm _ _
  -- the product of the norms is strictly smaller than `u 4 * v 4`
  have hnu : ‖proj4 u‖ = Real.sqrt (u 4 ^ 2 - 1) := by
    rw [← Real.sqrt_sq (norm_nonneg (proj4 u)), hPu]
  have hnv : ‖proj4 v‖ = Real.sqrt (v 4 ^ 2 - 1) := by
    rw [← Real.sqrt_sq (norm_nonneg (proj4 v)), hQv]
  have hnorms : ‖proj4 u‖ * ‖proj4 v‖ = Real.sqrt ((u 4 ^ 2 - 1) * (v 4 ^ 2 - 1)) := by
    rw [hnu, hnv, ← Real.sqrt_mul hA]
  have hprod : (u 4 ^ 2 - 1) * (v 4 ^ 2 - 1) < (u 4 * v 4) ^ 2 := by
    nlinarith [hx, hy]
  have hsqrt : Real.sqrt ((u 4 ^ 2 - 1) * (v 4 ^ 2 - 1)) < u 4 * v 4 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact hprod
  have hlt : ‖proj4 u‖ * ‖proj4 v‖ < u 4 * v 4 := by
    rw [hnorms]; exact hsqrt
  have hmain : lorentz u v = ⟪proj4 u, proj4 v⟫_ℝ - u 4 * v 4 := by
    rw [lorentz_eq_dotProduct_proj4, inner_eq_dotProduct]
  rw [hmain]
  linarith

end Work.HypModel
