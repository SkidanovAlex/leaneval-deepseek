import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.lorentz_dHypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `dHypOfUHS (uhsOfHyp P) ∘ dUhsOfHyp P` is the identity on `T_P upperSheet`

The upper half space chart and its inverse,
`hypOfUHS q = (q₀/q₃, q₁/q₃, q₂/q₃, (‖q‖²−1)/(2q₃), (‖q‖²+1)/(2q₃))` and
`uhsOfHyp P = (P₀,P₁,P₂,P₄−P₃)/(P₄−P₃)`, are mutually inverse on the upper sheet and the upper
half space.  Differentiating the relation at a point `P` of the hyperboloid therefore shows that
`dHypOfUHS (uhsOfHyp P) ∘ dUhsOfHyp P` fixes the tangent space `T_P = {v : ⟨P,v⟩ = 0}` — the
global derivative is not the identity on all of `ℝ⁵`, only on `T_P`.

Everything is an explicit rational identity in the coordinates of `P` and `v`: the first three
coordinates do not need the hypothesis `⟨P,v⟩ = 0`, while the last two reduce — using the
hyperboloid relation `⟨P,P⟩ = −1` and `⟨P,v⟩ = 0` — to `⟨P,v⟩ = 0` again after clearing the
denominators `P₄ − P₃` and `2`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- Coordinate `0` of the explicit derivative `dUhsOfHyp`. -/
@[simp] theorem dUhsOfHyp_apply_zero (P v : V5) :
    (dUhsOfHyp P v) 0 = v 0 / (P 4 - P 3) - P 0 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

/-- Coordinate `1` of the explicit derivative `dUhsOfHyp`. -/
@[simp] theorem dUhsOfHyp_apply_one (P v : V5) :
    (dUhsOfHyp P v) 1 = v 1 / (P 4 - P 3) - P 1 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

/-- Coordinate `2` of the explicit derivative `dUhsOfHyp`. -/
@[simp] theorem dUhsOfHyp_apply_two (P v : V5) :
    (dUhsOfHyp P v) 2 = v 2 / (P 4 - P 3) - P 2 * (v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

/-- Coordinate `3` of the explicit derivative `dUhsOfHyp`. -/
@[simp] theorem dUhsOfHyp_apply_three (P v : V5) :
    (dUhsOfHyp P v) 3 = -(v 4 - v 3) / (P 4 - P 3) ^ 2 := by
  simp [dUhsOfHyp]

/-- **`dHypOfUHS` is a left inverse of `dUhsOfHyp` on the tangent space of the upper sheet.**

For `P` on the hyperboloid and `v` in the tangent space `T_P upperSheet = {v : ⟨P,v⟩ = 0}`, the
composition of the two explicit differentials returns `v`.  This is the differential form of
`hypOfUHS (uhsOfHyp P) = P`. -/
theorem dHypOfUHS_comp_dUhsOfHyp {P : V5} (hP : P ∈ upperSheet) {v : V5}
    (hv : lorentz P v = 0) : dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v) = v := by
  have hδ : P 4 - P 3 ≠ 0 := ne_of_gt (upperSheet_four_sub_three_pos hP)
  -- the hyperboloid relation `⟨P,P⟩ = -1`, expanded
  have h03 : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 - P 4 ^ 2 = -1 := by
    have h := hP.1
    simp only [lorentz] at h
    nlinarith [h]
  -- the tangency relation `⟨P,v⟩ = 0`, expanded
  have hv' : P 0 * v 0 + P 1 * v 1 + P 2 * v 2 + P 3 * v 3 - P 4 * v 4 = 0 := by
    have h := hv
    simp only [lorentz] at h
    linarith [h]
  ext i
  fin_cases i
  · show (dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v)) (0 : Fin 5) = v (0 : Fin 5)
    simp only [dHypOfUHS_apply_zero, dUhsOfHyp_apply_zero, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_zero, uhsOfHyp_apply_three]
    field_simp
    ring
  · show (dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v)) (1 : Fin 5) = v (1 : Fin 5)
    simp only [dHypOfUHS_apply_one, dUhsOfHyp_apply_one, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_one, uhsOfHyp_apply_three]
    field_simp
    ring
  · show (dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v)) (2 : Fin 5) = v (2 : Fin 5)
    simp only [dHypOfUHS_apply_two, dUhsOfHyp_apply_two, dUhsOfHyp_apply_three,
      uhsOfHyp_apply_two, uhsOfHyp_apply_three]
    field_simp
    ring
  · show (dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v)) (3 : Fin 5) = v (3 : Fin 5)
    simp only [dHypOfUHS_apply_three, dUhsOfHyp_apply_zero, dUhsOfHyp_apply_one,
      dUhsOfHyp_apply_two, dUhsOfHyp_apply_three, uhsOfHyp_apply_zero, uhsOfHyp_apply_one,
      uhsOfHyp_apply_two, uhsOfHyp_apply_three, inner_E4_eq_coords, norm_sq_E4_eq_coords]
    field_simp
    linear_combination (2 * (P 4 - P 3)) * hv' - (v 4 - v 3) * h03
  · show (dHypOfUHS (uhsOfHyp P) (dUhsOfHyp P v)) (4 : Fin 5) = v (4 : Fin 5)
    simp only [dHypOfUHS_apply_four, dUhsOfHyp_apply_zero, dUhsOfHyp_apply_one,
      dUhsOfHyp_apply_two, dUhsOfHyp_apply_three, uhsOfHyp_apply_zero, uhsOfHyp_apply_one,
      uhsOfHyp_apply_two, uhsOfHyp_apply_three, inner_E4_eq_coords, norm_sq_E4_eq_coords]
    field_simp
    linear_combination (2 * (P 4 - P 3)) * hv' - (v 4 - v 3) * h03

end Work.HypModel
