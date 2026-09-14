import Mathlib
import Submission.Subspace.ApproxSpace

/-!
# Real systems viewed as complex systems

The approximation spaces `approxSpace L c Q` are defined for complex systems `L`.  A *real*
system `M` is viewed as the complex system `toC M`, and for real matrices the complex norm of a
value is the absolute value of the real value.  This file collects the elementary translations.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Submission.Subspace.RealRank

/-- The complexification of a real matrix. -/
def toC {σ : Type*} (M : Matrix σ σ ℝ) : σ → σ → ℂ := fun i k => ((M i k : ℝ) : ℂ)

lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h3 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h3]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- A value of a real system has the same complex norm as real absolute value. -/
lemma norm_toC_apply {σ : Type*} [Fintype σ] (M : Matrix σ σ ℝ) (x : σ → ℤ) (i : σ) :
    ‖∑ k, toC M i k * (x k : ℂ)‖ = |∑ k, M i k * (x k : ℝ)| := by
  have h : (∑ k, toC M i k * (x k : ℂ)) = ((∑ k, M i k * (x k : ℝ) : ℝ) : ℂ) := by
    simp only [toC]
    push_cast
    rfl
  rw [h, norm_ofReal_complex]

/-- The box of a real system, written with the complex norm. -/
lemma approxBox_toC {σ : Type*} [Fintype σ] (M : Matrix σ σ ℝ) (c : σ → ℝ) (Q : ℝ) :
    approxBox (toC M) c Q = {y : σ → ℤ | ∀ i, |∑ k, M i k * (y k : ℝ)| ≤ Q ^ (c i)} := by
  ext y
  simp only [approxBox, Set.mem_ofPred_eq]
  exact forall_congr' fun i => by rw [norm_toC_apply]

end Submission.Subspace.RealRank
