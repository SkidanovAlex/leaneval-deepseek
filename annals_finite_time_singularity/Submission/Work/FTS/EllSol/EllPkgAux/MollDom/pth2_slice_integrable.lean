import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem pth2_slice_integrable (G : ℝ → ℝ → ℝ)
    (hinn : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  intro z hz
  -- `w z ≠ 0` for `z > 0`, so the factor `(w z)^2` can be divided out.
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hc : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hinn z hz).mul_const ((Work.Spaces.w z) ^ 2)⁻¹ |>.congr ?_
  filter_upwards with θ
  rw [show (Work.Spaces.pth (Work.Spaces.pth G) z θ ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
      = (Work.Spaces.pth (Work.Spaces.pth G) z θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) by ring,
    mul_inv_cancel₀ hc, mul_one]

end Work.FTS.EllSol.EllPkgAux.MollDom
