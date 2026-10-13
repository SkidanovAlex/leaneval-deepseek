import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The weight identity behind `EDth_eq_wip`, pointwise: with `s = sin(2θ) ≥ 0` the
square of the angular weight `w·s^(-γ/2)` is `w²·s^(-γ)`. -/
private theorem sq_mul_rpow_neg_half (a w s γ : ℝ) (hs : 0 ≤ s) :
    (a * (w * s ^ (-(γ / 2)))) ^ 2 = a * a * (w ^ 2 * s ^ (-γ)) := by
  have h : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    rw [← Real.rpow_natCast (s ^ (-(γ / 2))) 2]
    calc (s ^ (-(γ / 2))) ^ (2 : ℝ) = s ^ ((-(γ / 2)) * 2) :=
          (Real.rpow_mul hs (-(γ / 2)) (2 : ℝ)).symm
      _ = s ^ (-γ) := by rw [show (-(γ / 2)) * 2 = -γ by ring]
  calc (a * (w * s ^ (-(γ / 2)))) ^ 2 = a ^ 2 * (w ^ 2 * (s ^ (-(γ / 2))) ^ 2) := by ring
    _ = a ^ 2 * (w ^ 2 * s ^ (-γ)) := by rw [h]
    _ = a * a * (w ^ 2 * s ^ (-γ)) := by ring

/-- `|D_θ f · w/√(sin(2θ)^γ)|²_{L²}` written in weighted inner-product form. -/
theorem EDth_eq_wip (α : ℝ) (f : ℝ → ℝ → ℝ) :
    EDth α f = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth f) (Spaces.Dth f) := by
  simp only [EDth, wtGam, Spaces.L2Sq, wip, Spaces.Iz, Spaces.Iθ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  exact sq_mul_rpow_neg_half (Spaces.Dth f z θ) (Spaces.w z) (Real.sin (2 * θ))
    (Spaces.gam α) hs

end Work.Coercivity
