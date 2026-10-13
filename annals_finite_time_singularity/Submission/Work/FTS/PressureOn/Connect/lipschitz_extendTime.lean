import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Connect.Clamp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem lipschitz_extendTime {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S t C : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C) (ht : t ∈ Set.Icc 0 S)
    (hlip : ∀ x, ∀ s ∈ Set.Icc 0 S, ‖v x s - v x t‖ ≤ C * |s - t|) :
    ∀ x, ∀ s : ℝ,
      ‖Work.FTS.PressureOn.Connect.extendTime v S x s
        - Work.FTS.PressureOn.Connect.extendTime v S x t‖ ≤ C * |s - t| := by
  intro x s
  have htc : clampt S t = t := clampt_eq_self_of_mem ht
  have hmem : clampt S s ∈ Set.Icc (0 : ℝ) S := clampt_mem_Icc hS s
  have h1 : ‖v x (clampt S s) - v x t‖ ≤ C * |clampt S s - t| := hlip x _ hmem
  have h2 : |clampt S s - t| ≤ |s - t| := by
    have h := abs_clampt_sub_le S s t
    rwa [htc] at h
  calc ‖Work.FTS.PressureOn.Connect.extendTime v S x s
        - Work.FTS.PressureOn.Connect.extendTime v S x t‖
      = ‖v x (clampt S s) - v x t‖ := by
        simp only [extendTime_apply, htc]
    _ ≤ C * |clampt S s - t| := h1
    _ ≤ C * |s - t| := mul_le_mul_of_nonneg_left h2 hC

end Work.FTS.PressureOn.Connect
