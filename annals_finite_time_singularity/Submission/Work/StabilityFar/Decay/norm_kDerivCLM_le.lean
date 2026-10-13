import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

/-- Pointwise bound for the derivative kernel `kDerivCLM b`: for every `v`,
`‖kDerivCLM b v‖ ≤ (4 / ‖b‖³) ‖v‖`, since
`kDerivCLM b v = ‖b‖⁻³ v - 3 ‖b‖⁻⁵ (b·v) b`. -/
private theorem norm_kDerivCLM_apply_le (b v : Work.LWP.R3) (hb : 0 < ‖b‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM b v‖ ≤ (4 / ‖b‖ ^ 3) * ‖v‖ := by
  have hE : Work.StabilityFar.Decay.kDerivCLM b v =
      (‖b‖ ^ (3 : ℕ))⁻¹ • v - (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • ((inner ℝ b v) • b) := by
    simp only [Work.StabilityFar.Decay.kDerivCLM, sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  calc ‖Work.StabilityFar.Decay.kDerivCLM b v‖
      = ‖(‖b‖ ^ (3 : ℕ))⁻¹ • v - (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • ((inner ℝ b v) • b)‖ := by
        rw [hE]
    _ ≤ ‖(‖b‖ ^ (3 : ℕ))⁻¹ • v‖ + ‖(3 * (‖b‖ ^ (5 : ℕ))⁻¹) • ((inner ℝ b v) • b)‖ :=
        norm_sub_le _ _
    _ = (‖b‖ ^ (3 : ℕ))⁻¹ * ‖v‖ + 3 * (‖b‖ ^ (5 : ℕ))⁻¹ * (‖inner ℝ b v‖ * ‖b‖) := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity)]
    _ ≤ (‖b‖ ^ (3 : ℕ))⁻¹ * ‖v‖ + 3 * (‖b‖ ^ (5 : ℕ))⁻¹ * ((‖b‖ * ‖v‖) * ‖b‖) := by
        gcongr
        exact norm_inner_le_norm b v
    _ = (4 / ‖b‖ ^ 3) * ‖v‖ := by
        field_simp
        ring

theorem norm_kDerivCLM_le (b : Work.LWP.R3) (m : ℝ) (hm : 0 < m) (hb : m ≤ ‖b‖) :
    ‖Work.StabilityFar.Decay.kDerivCLM b‖ ≤ 4 / m ^ 3 := by
  have hr : 0 < ‖b‖ := lt_of_lt_of_le hm hb
  have hmain : ∀ v : Work.LWP.R3,
      ‖Work.StabilityFar.Decay.kDerivCLM b v‖ ≤ (4 / ‖b‖ ^ 3) * ‖v‖ :=
    fun v => norm_kDerivCLM_apply_le b v hr
  have hbnd : ‖Work.StabilityFar.Decay.kDerivCLM b‖ ≤ 4 / ‖b‖ ^ 3 :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hmain
  have hmono : 4 / ‖b‖ ^ 3 ≤ 4 / m ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ (le_of_lt hm) hb 3
  linarith

end Work.StabilityFar.Decay
