import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FM.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Work

/-- `locG6 α L β` is the separable perturbation `locR α L β (z)·Γ(θ)` of
`Work.FTS.LocDataExt.locG_eq_locR_Gam`.  At `z = 2L + 1` the point lies beyond the bump support
`[3/4, 7/4]` and beyond the far cut-off `2L`, so the radial factor is the plain profile,
`locR α L β (2L+1) = -(α/c)·F_*(2L+1) ≠ 0` (`F_*(2L+1) > 0` and `1/10 ≤ c`), and the angular
factor `Γ(π/4)` is a positive `rpow`. -/
theorem locG6_apply_ne_zero {α L β : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.FTS.LocData6.locG6 α L β (2 * L + 1) (π / 4) ≠ 0 := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hz2 : (7 : ℝ) / 4 ≤ 2 * L + 1 := by linarith
  have hLR : 2 * L ≤ 2 * L + 1 := by linarith
  have hc : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hF : 0 < Work.FM.Fstar (2 * L + 1) := by
    rw [Work.FM.Fstar]
    apply div_pos
    · linarith
    · have h1 : 0 < 1 + (2 * L + 1) := by linarith
      positivity
  have hR : Work.FTS.LocDataExt.locR α L β (2 * L + 1) ≠ 0 := by
    rw [Work.FTS.LocDataExt.locR_apply,
      Work.FTS.LocDataExt.zfarR_eq_FM_Fstar_of_ge hLpos hLR,
      Work.FTS.LocDataExt.bumpZ_eq_zero_of_ge hz2, mul_zero, add_zero]
    exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ne_of_gt hα) (ne_of_gt hc)))
      (ne_of_gt hF)
  have hG : Work.Spaces.Gam α (π / 4) ≠ 0 := by
    rw [Work.Spaces.Gam]
    apply ne_of_gt
    apply Real.rpow_pos_of_pos
    have hsin : 0 < Real.sin (π / 4) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hcos : 0 < Real.cos (π / 4) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    positivity
  have hloc : ∀ z θ, Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α) z θ
      = Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ := by
    intro z θ
    rw [Work.FTS.LocDataExt.locG_eq_locR_Gam]
  change Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α) (2 * L + 1) (π / 4) ≠ 0
  rw [hloc (2 * L + 1) (π / 4)]
  exact mul_ne_zero hR hG

end Work.FTS.StrongEps.EpsE4Work
