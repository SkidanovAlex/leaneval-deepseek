import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

theorem Lneg_rpow (α : ℝ) (m : ℕ) {s z : ℝ} (hz : 0 < z)
    (hs : α ^ 2 * s ^ 2 + 5 * α * s = Work.FTS.PhiStar.Radial.lamR m) :
    Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α (fun t => t ^ s) z
      = - Work.FTS.PhiStar.Radial.lamR m * z ^ s := by
  have hz' : z ≠ 0 := ne_of_gt hz
  rw [Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg]
  -- the first two derivatives of `t ↦ t ^ s` at `z`
  have hd1 : deriv (fun t : ℝ => t ^ s) z = s * z ^ (s - 1) := Real.deriv_rpow_const z s
  have hd2 : deriv (deriv (fun t : ℝ => t ^ s)) z = s * ((s - 1) * z ^ (s - 1 - 1)) := by
    rw [Real.deriv_rpow_const' s]
    rw [deriv_const_mul s (Real.differentiableAt_rpow_const_of_ne (s - 1) hz')]
    rw [Real.deriv_rpow_const z (s - 1)]
  rw [hd2, hd1]
  -- `z ^ 2 * z ^ (s - 2) = z ^ s` and `z * z ^ (s - 1) = z ^ s`
  have hp1 : z ^ (2 : ℝ) * z ^ (s - 1 - 1) = z ^ s := by
    rw [← Real.rpow_add hz]; congr 1; ring
  have hp2 : z ^ (1 : ℝ) * z ^ (s - 1) = z ^ s := by
    rw [← Real.rpow_add hz]; congr 1; ring
  have hfac : α ^ 2 * z ^ 2 * (s * ((s - 1) * z ^ (s - 1 - 1)))
      + α * (5 + α) * z * (s * z ^ (s - 1))
      = α ^ 2 * s * (s - 1) * (z ^ 2 * z ^ (s - 1 - 1))
        + α * (5 + α) * s * (z * z ^ (s - 1)) := by ring
  rw [hfac]
  rw [show z ^ 2 * z ^ (s - 1 - 1) = z ^ s from by rw [← Real.rpow_natCast z 2]; exact hp1]
  rw [show z * z ^ (s - 1) = z ^ s from by
        nth_rewrite 1 [← Real.rpow_one z]; exact hp2]
  rw [show α ^ 2 * s * (s - 1) * z ^ s + α * (5 + α) * s * z ^ s
        = (α ^ 2 * s * (s - 1) + α * (5 + α) * s) * z ^ s from by ring]
  rw [show α ^ 2 * s * (s - 1) + α * (5 + α) * s = α ^ 2 * s ^ 2 + 5 * α * s from by ring]
  rw [hs]
  ring

end Work.EllipticEst.ModalSolution.RGW
