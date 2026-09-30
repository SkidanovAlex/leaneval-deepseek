import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein lift retracts the hyperboloid

`kleinOfHyp` is the central projection of the hyperboloid onto the affine plane `x₄ = 1`, and
`hypOfKlein` is the inverse parametrisation of the upper sheet by the open unit ball.  On the
upper sheet the two are mutually inverse: the projection of `P` lies in the unit ball and lifting
it back along the ray returns `P`.

Everything is a coordinate computation: writing `y = kleinOfHyp P` we have `y i = P i / P 4`, and
the Lorentz identity `-1 = ⟨P,P⟩` says `P₀² + P₁² + P₂² + P₃² = P₄² - 1`, so
`‖y‖² = 1 - (P₄)⁻¹²` and `√(1 - ‖y‖²) = (P₄)⁻¹ > 0`.  Multiplying the ray `(y,1)` by `P₄` gives
back `P`.
-/

noncomputable section

open scoped Matrix InnerProductSpace
open Matrix

namespace Work.HypModel

theorem hypOfKlein_kleinOfHyp {P : V5} (hP : P ∈ upperSheet) :
    hypOfKlein (kleinOfHyp P) = P := by
  have h4 : 0 < P 4 := hP.2
  have h4ne : P 4 ≠ 0 := ne_of_gt h4
  -- The Lorentz identity `⟨P,P⟩ = -1` as a statement about squares of coordinates.
  have hsos : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 = P 4 ^ 2 - 1 := by
    have h := hP.1
    simp only [lorentz] at h
    nlinarith
  -- The norm of the first four coordinates.
  have hproj : ‖proj4 P‖ ^ 2 = P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    simp [dotProduct, proj4, Fin.sum_univ_four]
    ring
  -- `kleinOfHyp P` is the scalar multiple `(P 4)⁻¹ • proj4 P`.
  have hnormsq : ‖kleinOfHyp P‖ ^ 2 = ((P 4)⁻¹) ^ 2 * ‖proj4 P‖ ^ 2 := by
    rw [kleinOfHyp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnorm : ‖kleinOfHyp P‖ ^ 2 = 1 - ((P 4)⁻¹) ^ 2 := by
    rw [hnormsq, hproj, hsos]
    field_simp
  -- Hence the Klein parameter of `P` is the reciprocal of the height of `P`.
  have hsqrt : Real.sqrt (1 - ‖kleinOfHyp P‖ ^ 2) = (P 4)⁻¹ := by
    have h : 1 - ‖kleinOfHyp P‖ ^ 2 = ((P 4)⁻¹) ^ 2 := by rw [hnorm]; ring
    rw [h, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr h4)]
  have hc : (Real.sqrt (1 - ‖kleinOfHyp P‖ ^ 2))⁻¹ = P 4 := by
    rw [hsqrt, inv_inv]
  -- Coordinatewise the lift is `P ↦ P 4 * (P i / P 4) = P i`.
  ext i
  fin_cases i <;> simp [hc, h4ne]

end Work.HypModel
