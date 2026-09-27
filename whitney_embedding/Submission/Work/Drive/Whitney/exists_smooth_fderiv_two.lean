import Mathlib

namespace Work.Drive.Whitney

open scoped ContDiff Topology
open Filter Metric

/-- **Prescribed derivatives at two distinct points, into a subspace.** -/
theorem exists_smooth_fderiv_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : Submodule ℝ E} (z₁ z₂ : E) (hz : z₁ ≠ z₂)
    (T₁ T₂ : E →L[ℝ] E) (hT₁ : ∀ v : E, T₁ v ∈ N) (hT₂ : ∀ v : E, T₂ v ∈ N) :
    ∃ g : E → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∀ y : E, g y ∈ N) ∧
      fderiv ℝ g z₁ = T₁ ∧ fderiv ℝ g z₂ = T₂ := by
  have hd : 0 < dist z₁ z₂ := dist_pos.mpr hz
  -- A smooth bump which is `1` near `z₁` and `0` near `z₂`.
  let f : ContDiffBump z₁ := ⟨dist z₁ z₂ / 4, dist z₁ z₂ / 2, by linarith, by linarith⟩
  have hf1 : ∀ y ∈ Metric.closedBall z₁ (dist z₁ z₂ / 4), (f : E → ℝ) y = 1 :=
    fun y hy => f.one_of_mem_closedBall hy
  have hf0 : ∀ y, dist z₁ z₂ / 2 ≤ dist y z₁ → (f : E → ℝ) y = 0 :=
    fun y hy => f.zero_of_le_dist hy
  -- The interpolant: it agrees with `T₁ (· - z₁)` near `z₁` and with `T₂ (· - z₂)` near `z₂`.
  refine ⟨fun y => f y • T₁ (y - z₁) + (1 - f y) • T₂ (y - z₂), ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f : E → ℝ) := f.contDiff
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => T₁ (y - z₁)) :=
      T₁.contDiff.comp (contDiff_id.sub contDiff_const)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => (1 : ℝ) - f y) :=
      contDiff_const.sub hf
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => T₂ (y - z₂)) :=
      T₂.contDiff.comp (contDiff_id.sub contDiff_const)
    exact (hf.smul h1).add (h2.smul h3)
  · -- values in the subspace `N`
    intro y
    exact N.add_mem (N.smul_mem (f y) (hT₁ (y - z₁))) (N.smul_mem (1 - f y) (hT₂ (y - z₂)))
  · -- derivative at `z₁`
    have hev : (fun y : E => f y • T₁ (y - z₁) + (1 - f y) • T₂ (y - z₂))
        =ᶠ[𝓝 z₁] (fun y : E => T₁ (y - z₁)) := by
      filter_upwards [Metric.closedBall_mem_nhds_of_mem
        (show z₁ ∈ Metric.ball z₁ (dist z₁ z₂ / 4) by
          simp only [Metric.mem_ball, dist_self]; linarith)] with y hy
      rw [hf1 y hy, one_smul, sub_self, zero_smul, add_zero]
    rw [Filter.EventuallyEq.fderiv_eq hev]
    have hdf : HasFDerivAt (fun y : E => T₁ (y - z₁)) T₁ z₁ := by
      have h := (ContinuousLinearMap.hasFDerivAt T₁).comp z₁ (hasFDerivAt_sub_const z₁)
      simpa [Function.comp_def] using h
    exact hdf.fderiv
  · -- derivative at `z₂`
    have hev : (fun y : E => f y • T₁ (y - z₁) + (1 - f y) • T₂ (y - z₂))
        =ᶠ[𝓝 z₂] (fun y : E => T₂ (y - z₂)) := by
      filter_upwards [Metric.ball_mem_nhds z₂ (show 0 < dist z₁ z₂ / 4 by linarith)] with y hy
      have hy0 : (f : E → ℝ) y = 0 := by
        apply hf0
        have h1 : dist y z₂ < dist z₁ z₂ / 4 := hy
        have h2 : dist z₁ z₂ ≤ dist z₁ y + dist y z₂ := dist_triangle _ _ _
        rw [dist_comm y z₁]
        linarith
      rw [hy0, zero_smul, sub_zero, one_smul, zero_add]
    rw [Filter.EventuallyEq.fderiv_eq hev]
    have hdf : HasFDerivAt (fun y : E => T₂ (y - z₂)) T₂ z₂ := by
      have h := (ContinuousLinearMap.hasFDerivAt T₂).comp z₂ (hasFDerivAt_sub_const z₂)
      simpa [Function.comp_def] using h
    exact hdf.fderiv

end Work.Drive.Whitney
