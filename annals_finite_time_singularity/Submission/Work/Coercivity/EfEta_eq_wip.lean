import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem EfEta_eq_wip (f : ℝ → ℝ → ℝ) :
    EfEta f = wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) f f := by
  simp only [EfEta, wtEta, wtGam, Spaces.L2Sq, wip]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro z hz
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  dsimp only
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hs : ((Real.sin (2 * θ)) ^ (-(Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Spaces.eta / 2))) 2,
      ← Real.rpow_mul hsin]
    rw [show (-(Spaces.eta / 2)) * ((2 : ℕ) : ℝ) = -Spaces.eta by push_cast; ring]
  rw [mul_pow, mul_pow, hs]
  ring

end Work.Coercivity
