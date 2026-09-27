import Mathlib

set_option autoImplicit false

/-!
# Bounds for continuous compactly supported functions

A continuous function with compact support into a normed space is bounded in norm; if it is
differentiable with continuous derivative, it is globally Lipschitz.
-/

open scoped Topology NNReal
open Function

namespace Work.ODE

/-- A continuous compactly supported function into a normed space is bounded in norm. -/
theorem exists_norm_le_of_hasCompactSupport {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨r, hr⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : F)).mp ((hc.image hf).isBounded)
    rcases hne with ⟨x₀, hx₀⟩
    have hr0 : 0 ≤ r :=
      (norm_nonneg _).trans (mem_closedBall_zero_iff.mp (hr ⟨x₀, hx₀, rfl⟩))
    refine ⟨r, hr0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport f
    · exact mem_closedBall_zero_iff.mp (hr ⟨x, hx, rfl⟩)
    · have h0 : f x = 0 := Function.notMem_support.mp fun h => hx (subset_closure h)
      rw [h0, norm_zero]
      exact hr0
  · refine ⟨0, le_rfl, fun x => ?_⟩
    have hx : x ∉ tsupport f := fun h => hne ⟨x, h⟩
    have h0 : f x = 0 := Function.notMem_support.mp fun h => hx (subset_closure h)
    simp [h0]

/-- A continuous compactly supported function into a normed space is bounded in nnnorm. -/
theorem exists_nnnorm_le_of_hasCompactSupport {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ M : NNReal, ∀ x, ‖f x‖₊ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_of_hasCompactSupport hf hc
  refine ⟨M.toNNReal, fun x => ?_⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]
  exact hM x

/-- A `C¹` function with compact support between normed spaces is globally Lipschitz. -/
theorem exists_lipschitzWith_of_contDiff_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ L : NNReal, LipschitzWith L f := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hfc : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨L, hL⟩ := exists_nnnorm_le_of_hasCompactSupport hfd hfc
  exact ⟨L, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num)) hL⟩

end Work.ODE
