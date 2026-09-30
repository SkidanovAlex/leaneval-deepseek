import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The central projection of the upper sheet lies in the open unit ball

`kleinOfHyp P = (P 4)⁻¹ • proj4 P` is the central projection of the point `P` of the hyperboloid
onto the affine plane `x₄ = 1`.  For `P` on the upper sheet the Lorentz identity `⟨P,P⟩ = -1` reads
`P₀² + P₁² + P₂² + P₃² = P₄² - 1`, so with `y = kleinOfHyp P`,

`‖y‖² = (P₄)⁻² ‖proj4 P‖² = (P₄)⁻² (P₄² - 1) = 1 - (P₄)⁻² < 1`,

because `P₄ > 0`; as `‖y‖ ≥ 0` this forces `‖y‖ < 1`, i.e. `y ∈ ball`.
-/

noncomputable section

namespace Work.HypModel

theorem kleinOfHyp_mem_ball {P : V5} (hP : P ∈ upperSheet) : kleinOfHyp P ∈ ball := by
  have h4 : 0 < P 4 := hP.2
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
  change ‖kleinOfHyp P‖ < 1
  have hlt : ‖kleinOfHyp P‖ ^ 2 < 1 := by
    rw [hnorm]
    have hpos : 0 < ((P 4)⁻¹) ^ 2 := by positivity
    linarith
  nlinarith [norm_nonneg (kleinOfHyp P)]

end Work.HypModel
