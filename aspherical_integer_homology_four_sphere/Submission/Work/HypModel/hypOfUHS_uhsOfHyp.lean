import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `hypOfUHS` is a left inverse of `uhsOfHyp` on the upper sheet

The upper half space chart of hyperbolic 4-space,

`hypOfUHS q = (q₀/q₃, q₁/q₃, q₂/q₃, (‖q‖²−1)/(2q₃), (‖q‖²+1)/(2q₃))`,

is injective on `{q : 0 < q 3}`; here we record that its explicit inverse `uhsOfHyp` really is a
section: for every point `P` of the hyperboloid `upperSheet`, `hypOfUHS (uhsOfHyp P) = P`.

The only geometry used is the Lorentz identity `P₀²+P₁²+P₂²+P₃²−P₄² = −1` characterising the
hyperboloid and the fact that `P₄ − P₃ > 0` on the upper sheet, so that `(P₄−P₃)⁻¹` is a legitimate
height.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix

theorem hypOfUHS_uhsOfHyp {P : V5} (hP : P ∈ upperSheet) : hypOfUHS (uhsOfHyp P) = P := by
  have hδpos : 0 < P 4 - P 3 := upperSheet_four_sub_three_pos hP
  have hδ : P 4 - P 3 ≠ 0 := ne_of_gt hδpos
  -- the Lorentz identity for a point of the hyperboloid
  have hsq : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 - P 4 ^ 2 = -1 := by
    have h := hP.1
    simp only [lorentz] at h
    nlinarith [h]
  -- hence `P₀²+P₁²+P₂²+1 = P₄²−P₃² = (P₄−P₃)(P₄+P₃)`
  have hN : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + 1 = (P 4 - P 3) * (P 4 + P 3) := by
    nlinarith [hsq]
  have hsδ : (P 4 - P 3)⁻¹ * (P 4 - P 3) = 1 := inv_mul_cancel₀ hδ
  -- the square norm of the explicit inverse point
  have hnorm : ‖!₂[P 0 * (P 4 - P 3)⁻¹, P 1 * (P 4 - P 3)⁻¹, P 2 * (P 4 - P 3)⁻¹, (P 4 - P 3)⁻¹]‖ ^ 2
      = (P 4 - P 3)⁻¹ ^ 2 * (P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + 1) := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
    simp only [Fin.isValue, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  ext i
  fin_cases i
  · simp [hypOfUHS, uhsOfHyp]
    rw [mul_assoc, hsδ, mul_one]
  · simp [hypOfUHS, uhsOfHyp]
    rw [mul_assoc, hsδ, mul_one]
  · simp [hypOfUHS, uhsOfHyp]
    rw [mul_assoc, hsδ, mul_one]
  · simp [hypOfUHS, uhsOfHyp]
    rw [hnorm]
    field_simp
    nlinarith [hN, hsδ, sq_nonneg (P 4 - P 3)]
  · simp [hypOfUHS, uhsOfHyp]
    rw [hnorm]
    field_simp
    nlinarith [hN, hsδ, sq_nonneg (P 4 - P 3)]

end Work.HypModel
