import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic.Decomp

/-- A `C^∞` function with compact support on `ℝ³` is bounded, and its derivative is
bounded by the same constant. -/
theorem exists_bound_fderiv {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ENat) f) (hcs : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |f x| ≤ M) ∧ ∀ (x v : EuclideanSpace ℝ (Fin 3)),
      ‖fderiv ℝ f x v‖ ≤ M * ‖v‖ := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hf.continuous
  obtain ⟨D, hD⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨max (max C D) 0, le_max_right _ _, ?_, ?_⟩
  · intro x
    simp only [Real.norm_eq_abs] at hC
    exact (hC x).trans (le_trans (le_max_left C D) (le_max_left (max C D) 0))
  · intro x v
    refine (ContinuousLinearMap.le_opNorm (fderiv ℝ f x) v).trans ?_
    exact mul_le_mul_of_nonneg_right
      ((hD x).trans (le_trans (le_max_right C D) (le_max_left (max C D) 0))) (norm_nonneg v)

end Work.BSKinetic.Decomp
