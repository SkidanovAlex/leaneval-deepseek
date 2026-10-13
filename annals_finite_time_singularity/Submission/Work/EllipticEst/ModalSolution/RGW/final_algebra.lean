import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

theorem final_algebra (α : ℝ) (hα : 0 < α) (m : ℕ) {t A B : ℝ} (ht : 0 < t) :
    1 / (α * (4 * (m : ℝ) + 5)) * Work.EllipticEst.ModalSolution.RadGreenWeak.pwt α t *
      (t ^ ((2 * (m : ℝ) + 5) / α - 1)
          * (-(Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m
                * t ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m - 1) * A
              - t ^ Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m * B))
        + t ^ (-(2 * (m : ℝ) / α) - 1)
          * (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m
                * t ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m - 1) * A
              - t ^ Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m * B))
      = A * Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α t := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- unfold `pwt = α²t²·t^q`, `wgt = t^q`, `sM = -(2m+5)/α`, `sP = 2m/α`
  unfold Work.EllipticEst.ModalSolution.RadGreenWeak.pwt
    Work.EllipticEst.ModalSolution.RadGreenWeak.wgt
    Work.EllipticEst.ModalSolution.RadGreenWeak.sM
    Work.EllipticEst.ModalSolution.RadGreenWeak.sP
  -- set the two indicial exponents as opaque atoms (so `ring` can reassociate products;
  -- it cannot see through the division by `α`), keeping `M`, `P` for their values.
  set M : ℝ := -(2 * (m : ℝ) + 5) / α with hM
  set P : ℝ := 2 * (m : ℝ) / α with hP
  have hMs : (2 * (m : ℝ) + 5) / α = -M := by rw [hM]; ring
  rw [hMs]
  -- merging the powers of `t`: `t ^ (-M-1) * t ^ (M-1) = t ^ (-2)`, `t ^ (-M-1) * t ^ M = t ^ (-1)`,
  -- and likewise for `P`.
  have e1 : t ^ (-M - 1) * t ^ (M - 1) = t ^ (-2 : ℝ) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have e2 : t ^ (-M - 1) * t ^ M = t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have e3 : t ^ (-P - 1) * t ^ (P - 1) = t ^ (-2 : ℝ) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have e4 : t ^ (-P - 1) * t ^ P = t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  -- the `M`-half of the bracket collapses to `-M·A/t² + B/t`
  have hX : t ^ (-M - 1) * (-(M * t ^ (M - 1) * A - t ^ M * B))
      = -(M * A * t ^ (-2 : ℝ)) + B * t ^ (-1 : ℝ) := by
    rw [mul_neg, mul_sub]
    rw [show t ^ (-M - 1) * (M * t ^ (M - 1) * A)
          = M * A * (t ^ (-M - 1) * t ^ (M - 1)) from by ring, e1]
    rw [show t ^ (-M - 1) * (t ^ M * B) = B * (t ^ (-M - 1) * t ^ M) from by ring, e2]
    ring
  -- the `P`-half collapses to `P·A/t² - B/t` (the goal is already closed by the two rewrites)
  have hY : t ^ (-P - 1) * (P * t ^ (P - 1) * A - t ^ P * B)
      = P * A * t ^ (-2 : ℝ) - B * t ^ (-1 : ℝ) := by
    rw [mul_sub]
    rw [show t ^ (-P - 1) * (P * t ^ (P - 1) * A)
          = P * A * (t ^ (-P - 1) * t ^ (P - 1)) from by ring, e3]
    rw [show t ^ (-P - 1) * (t ^ P * B) = B * (t ^ (-P - 1) * t ^ P) from by ring, e4]
  -- the whole bracket: the `B`-terms cancel and `sP - sM = P - M`
  have hbr : t ^ (-M - 1) * (-(M * t ^ (M - 1) * A - t ^ M * B))
        + t ^ (-P - 1) * (P * t ^ (P - 1) * A - t ^ P * B)
      = (P - M) * A * t ^ (-2 : ℝ) := by
    rw [hX, hY]; ring
  rw [hbr]
  -- write `t ^ (-2)` as an inverse so that `field_simp` clears it together with the prefactor
  have hinv : t ^ (-2 : ℝ) = ((t : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt ht), Real.rpow_two]
  rw [hinv]
  -- `(P - M)·α = (4m + 5)`
  have hPM : (P - M) * α = 4 * (m : ℝ) + 5 := by
    rw [hP, hM]; field_simp; ring
  have hden : α * (4 * (m : ℝ) + 5) ≠ 0 := by
    have hp : (0 : ℝ) < α * (4 * (m : ℝ) + 5) := by positivity
    exact ne_of_gt hp
  have ht2 : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
  field_simp
  rw [← hPM]
  ring

end Work.EllipticEst.ModalSolution.RGW
