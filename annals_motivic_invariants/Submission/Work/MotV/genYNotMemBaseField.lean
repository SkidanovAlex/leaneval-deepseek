import Mathlib
import Submission.Work.MotV.DerivZeroDefs
import Submission.Work.MotC2.genY_not_ratFunc_genX

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

theorem genYNotMemBaseField (N : Type*) [Field N] (E : WeierstrassCurve N) [E.IsElliptic] :
    Work.MotC2.genY E ∉ Work.MotV.baseField E := by
  intro h
  rw [Work.MotV.mem_baseField_iff] at h
  obtain ⟨w, hw⟩ := h
  refine Work.MotC2.genY_not_ratFunc_genX N E ⟨w.num, w.denom, RatFunc.denom_ne_zero w, ?_⟩
  have hden : Work.MotC2.xPhi E w.denom ≠ 0 := fun h0 =>
    RatFunc.denom_ne_zero w (Work.MotC2.xPhi_injective E (by simp [h0]))
  have hden' : (algebraMap (Polynomial N) (Work.MotC2.Func E)) w.denom ≠ 0 := by
    rw [← Work.MotC2.xPhi_apply]
    exact hden
  have hmain : Work.MotC2.xPhi E w.num / Work.MotC2.xPhi E w.denom = Work.MotC2.genY E := by
    have h1 := congrArg (Work.MotC2.xPsi E) (RatFunc.num_div_denom w)
    simp only [map_div₀] at h1
    rw [Work.MotC2.xPsi_apply_algebraMap, Work.MotC2.xPsi_apply_algebraMap, hw] at h1
    exact h1
  rw [Work.MotC2.xPhi_apply, Work.MotC2.xPhi_apply] at hmain
  exact (div_eq_iff hden').mp hmain

end Work.MotV
