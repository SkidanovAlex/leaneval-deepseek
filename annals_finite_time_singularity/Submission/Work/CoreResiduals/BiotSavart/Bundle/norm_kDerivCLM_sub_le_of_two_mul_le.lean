import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

open Work.StabilityFar.Decay (kDerivCLM)

/-- **Pointwise Lipschitz estimate for the Biot–Savart derivative kernel away from two points.**
If `0 < δ`, `‖x - y‖ ≤ δ` and `2δ ≤ ‖a - y‖`, then both `x - a` and `y - a` have norm at least
`‖a - y‖ / 2`, so `norm_kDerivCLM_sub_le` at `m = ‖a - y‖ / 2` gives the degree-`-4` bound
`‖kDerivCLM (x-a) - kDerivCLM (y-a)‖ ≤ 64/(‖a-y‖/2)^4 · ‖x-y‖ ≤ 1024 δ / ‖a-y‖^4`. -/
theorem norm_kDerivCLM_sub_le_of_two_mul_le {δ : ℝ} (hδ : 0 < δ) {x y a : Work.LWP.R3}
    (hxy : ‖x - y‖ ≤ δ) (ha : 2 * δ ≤ ‖a - y‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM (x - a) - Work.StabilityFar.Decay.kDerivCLM (y - a)‖
      ≤ 1024 * δ / ‖a - y‖ ^ 4 := by
  have hr : 0 < ‖a - y‖ := by linarith
  have hm : 0 < ‖a - y‖ / 2 := by linarith
  have hle : ‖x - y‖ ≤ ‖a - y‖ / 2 := by linarith
  -- `x - a` is far from the origin: `‖a - y‖ ≤ ‖x - a‖ + ‖x - y‖`.
  have hxb : ‖a - y‖ / 2 ≤ ‖x - a‖ := by
    have h : ‖a - y‖ ≤ ‖x - a‖ + ‖x - y‖ := by
      have h1 : a - y = (a - x) + (x - y) := by abel
      rw [h1]
      calc ‖(a - x) + (x - y)‖ ≤ ‖a - x‖ + ‖x - y‖ := norm_add_le _ _
        _ = ‖x - a‖ + ‖x - y‖ := by rw [norm_sub_rev a x]
    linarith
  -- `y - a` itself has norm at least `‖a - y‖ / 2`.
  have hyb : ‖a - y‖ / 2 ≤ ‖y - a‖ := by
    rw [norm_sub_rev y a]
    linarith
  have h := Work.StabilityFar.Decay.norm_kDerivCLM_sub_le (x - a) (y - a) (‖a - y‖ / 2) hm hxb hyb
  have hsub : (x - a) - (y - a) = x - y := by abel
  rw [hsub] at h
  have hconst : 64 / (‖a - y‖ / 2) ^ 4 = 1024 / ‖a - y‖ ^ 4 := by
    rw [div_pow]
    field_simp
    ring
  rw [hconst] at h
  calc ‖kDerivCLM (x - a) - kDerivCLM (y - a)‖
      ≤ 1024 / ‖a - y‖ ^ 4 * ‖x - y‖ := h
    _ ≤ 1024 / ‖a - y‖ ^ 4 * δ := by gcongr
    _ = 1024 * δ / ‖a - y‖ ^ 4 := by ring

end Work.CoreResiduals.BiotSavart.Bundle
