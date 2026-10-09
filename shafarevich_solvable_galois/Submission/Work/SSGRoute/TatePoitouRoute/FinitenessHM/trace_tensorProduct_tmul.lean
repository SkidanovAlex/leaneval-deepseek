/-
# Trace of a base-changed element

`Tr_{K ⊗[ℚ] F / F}(z ⊗ s) = s * (Tr_{K/ℚ} z)`.

This is the trace-compatibility of the base change `K ↦ K ⊗[ℚ] F`, and one of the two inputs of the
local–global trace identity `∑_{Q | p} Tr_{K_Q/ℚ_p}(z) = Tr_{K/ℚ}(z)`
(`FinitenessHM/sum_trace_adicCompletion_eq_trace.lean`).
-/
import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.completionSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Trace of a base-changed element.**  For `K` a finite extension of `ℚ` and `F` a `ℚ`-algebra,
the trace over `F` of the base change `z ⊗ s ∈ K ⊗[ℚ] F` is `s · Tr_{K/ℚ}(z)`. -/
theorem trace_tensorProduct_tmul {K F : Type*} [Field K] [Field F] [Algebra ℚ K] [Algebra ℚ F]
    [FiniteDimensional ℚ K] (z : K) (s : F) :
    Algebra.trace F (TensorProduct ℚ K F) (TensorProduct.mk ℚ K F z s)
      = s * algebraMap ℚ F (Algebra.trace ℚ K z) := by
  have key : Algebra.trace F (TensorProduct ℚ F K) (TensorProduct.mk ℚ F K s z)
      = s * algebraMap ℚ F (Algebra.trace ℚ K z) := by
    have hlmul : Algebra.lmul F (TensorProduct ℚ F K) (TensorProduct.mk ℚ F K s z)
        = s • LinearMap.baseChange F (Algebra.lmul ℚ K z) := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s' x' =>
        simp only [TensorProduct.mk_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
          LinearMap.smul_apply, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy =>
        rw [LinearMap.smul_apply] at hx hy
        rw [map_add, map_add, LinearMap.smul_apply, LinearMap.smul_apply, ← hx, ← hy]
    rw [Algebra.trace_apply, hlmul, map_smul, LinearMap.trace_baseChange, Algebra.trace_apply,
      smul_eq_mul]
  have hfs : (Algebra.TensorProduct.commRight ℚ F K).symm (TensorProduct.mk ℚ K F z s)
      = TensorProduct.mk ℚ F K s z := rfl
  have hcomm : Algebra.trace F (TensorProduct ℚ F K) (TensorProduct.mk ℚ F K s z)
      = Algebra.trace F (TensorProduct ℚ K F) (TensorProduct.mk ℚ K F z s) := by
    conv_lhs => rw [← hfs]
    exact Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.commRight ℚ F K).symm
      (TensorProduct.mk ℚ K F z s)
  exact hcomm.symm.trans key

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
