import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.psi2_T2

namespace Work.Asymptotics.KMinusFunnel

open UpperHalfPlane

theorem LS_vadd_int_norm (ℓ : Work.Kernels.LogLambdaData) (m : ℤ) (z : UpperHalfPlane) :
    ‖ℓ.L_S ((m : ℝ) +ᵥ z)‖ = ‖ℓ.L_S z‖ := by
  -- Translation by `1` changes the sign of `𝓛_S` (the `T`-transformation law).
  have step_pos : ∀ w : ℍ, ℓ.L_S ((1 : ℝ) +ᵥ w) = - ℓ.L_S w :=
    fun w => Work.Kernels.KernelFacts.L_S_vadd_one ℓ w
  -- Translation by `-1` changes the sign of `𝓛_S` too.
  have step_neg : ∀ w : ℍ, ℓ.L_S ((-1 : ℝ) +ᵥ w) = - ℓ.L_S w := by
    intro w
    have h : ℓ.L_S w = - ℓ.L_S ((-1 : ℝ) +ᵥ w) := by
      have hh := Work.Kernels.KernelFacts.L_S_vadd_one ℓ ((-1 : ℝ) +ᵥ w)
      rwa [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w from by
        rw [← add_vadd, add_neg_cancel, zero_vadd]] at hh
    exact (neg_eq_iff_eq_neg.mpr h).symm
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro i hh
    have hcast : ((↑i + 1 : ℤ) : ℝ) = 1 + (i : ℝ) := by push_cast; ring
    rw [hcast, add_vadd, step_pos, norm_neg]
    simpa using hh
  · intro i hh
    have hcast : ((-↑i - 1 : ℤ) : ℝ) = -1 + -(i : ℝ) := by push_cast; ring
    rw [hcast, add_vadd, step_neg, norm_neg]
    simpa using hh

end Work.Asymptotics.KMinusFunnel
