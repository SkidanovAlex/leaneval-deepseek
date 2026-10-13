import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open Work.LWP

/-- **The value of the kernel `kDerivCLM` on a ray.**

For `s > 0` and a unit vector `ω`, the Fréchet derivative of the Newtonian kernel
`kf b = ‖b‖⁻³ • b` at the point `b = s • ω` is
`(s ^ 3)⁻¹ • (Id − 3 (innerSL ℝ ω).smulRight ω)`: the radial factor `‖b‖⁻³ = s⁻³` and the
angular factor `Id − 3 ω⊗ω` separate, because `‖ω‖ = 1`. -/
theorem kDerivCLM_smul_sphere (s : Set.Ioi (0 : ℝ))
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    Work.StabilityFar.Decay.kDerivCLM ((s : ℝ) • (ω : Work.LWP.R3))
      = (((s : ℝ)) ^ 3)⁻¹ •
          (ContinuousLinearMap.id ℝ Work.LWP.R3
            - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3)) := by
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hω : ‖(ω : Work.LWP.R3)‖ = 1 := by
    have h := ω.2
    simp only [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have hnorm : ‖(s : ℝ) • (ω : Work.LWP.R3)‖ = (s : ℝ) := by
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  ext v
  simp only [Work.StabilityFar.Decay.kDerivCLM, hnorm, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_sub]
  rw [real_inner_smul_left]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sub]
  simp only [Pi.sub_apply, Pi.smul_apply]
  field_simp
  ring_nf
  field_simp

theorem ray_indicator_kDerivCLM {r ρ : ℝ}
    (s : Set.Ioi (0 : ℝ)) (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r).indicator
        (fun b => Work.StabilityFar.Decay.kDerivCLM b) ((s : ℝ) • (ω : Work.LWP.R3))
      = (if r ≤ (s : ℝ) ∧ (s : ℝ) < ρ then (((s : ℝ)) ^ 3)⁻¹ else 0)
          • (ContinuousLinearMap.id ℝ Work.LWP.R3
              - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3)) := by
  have hs : (0 : ℝ) < (s : ℝ) := s.2
  have hω : ‖(ω : Work.LWP.R3)‖ = 1 := by
    have h := ω.2
    simp only [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have hnorm : ‖(s : ℝ) • (ω : Work.LWP.R3)‖ = (s : ℝ) := by
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  have hkey := kDerivCLM_smul_sphere s ω
  by_cases h : r ≤ (s : ℝ) ∧ (s : ℝ) < ρ
  · have hmem : (s : ℝ) • (ω : Work.LWP.R3)
        ∈ Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r := by
      simp only [Set.mem_diff, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
      exact ⟨h.2, not_lt.mpr h.1⟩
    rw [Set.indicator_of_mem hmem, if_pos h, hkey]
  · have hnotmem : (s : ℝ) • (ω : Work.LWP.R3)
        ∉ Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r := by
      intro con
      have h' : (s : ℝ) < ρ ∧ ¬ (s : ℝ) < r := by
        simpa only [Set.mem_diff, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm] using con
      exact h ⟨not_lt.mp h'.2, h'.1⟩
    rw [Set.indicator_of_notMem hnotmem, if_neg h]
    exact (zero_smul ℝ (ContinuousLinearMap.id ℝ Work.LWP.R3
      - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3))).symm

end Work.CoreResiduals.BiotSavart
