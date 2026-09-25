import Mathlib
import Submission.Work.NN.Core.bmPotential_dbarDefect_eq

namespace Work.NN.Core

open scoped NNReal ENNReal
open MeasureTheory Set Filter

noncomputable section

/-- A compactly supported function vanishes off a ball of some positive radius. -/
private lemma exists_radius_forall_le_norm_of_hasCompactSupport {n : ℕ}
    {W : (Fin n → ℂ) → ℂ} (hc : HasCompactSupport W) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → W x = 0 := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  refine ⟨max r 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hx0
  have hmem : x ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hx0)
  have h1 : ‖x‖ ≤ r := by
    have h := hr hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have h2 : r ≤ max r 0 := le_max_left _ _
  linarith

/-- The Bochner–Martinelli divergence formula in the "potential of `∂̄`" form: for a compactly
supported `C¹` function `W` and a point `z`,
`bmPotential (∂̄ W) z = bmGamma n · W z`. -/
theorem bmPotential_dbarCoord_eq_bmGamma_mul {n : ℕ} (hn : 0 < n) {W : (Fin n → ℂ) → ℂ}
    (hW : ContDiff ℝ 1 W) (hc : HasCompactSupport W) (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.bmGamma n * W z
      = Work.CR.Flat.Cauchy.bmPotential (fun l y => Work.CR.Flat.dbarCoord l W y) z := by
  obtain ⟨R, hRpos, hR⟩ := exists_radius_forall_le_norm_of_hasCompactSupport hc
  -- The divergence formula applied to the translate `y ↦ W (z + y)`.
  have hkey : (∑ k, ∫ x : Fin n → ℂ,
        Work.CR.Flat.Cauchy.bmKernel k x * Work.CR.Flat.dbarCoord k (fun y => W (z + y)) x)
      = Work.CR.Flat.Cauchy.bmGamma n * W z := by
    have hg : ContDiff ℝ 1 (fun y : Fin n → ℂ => W (z + y)) :=
      hW.comp (contDiff_const.add contDiff_id)
    have hgs : ∀ x : Fin n → ℂ, R + ‖z‖ ≤ ‖x‖ → W (z + x) = 0 := by
      intro x hx
      refine hR (z + x) ?_
      have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
        calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
      linarith
    have hh := Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps hn (by positivity)
      hg hgs (Work.CR.Flat.Cauchy.integrable_bmWeight hn).1
      (fun ε hε => Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral hn (by positivity) hg hgs hε)
    simpa using hh
  -- `bmPot` of `∂̄ W`, with the singularity translated to the origin.
  have hmain : (∑ k, ∫ x : Fin n → ℂ,
        Work.CR.Flat.Cauchy.bmKernel k x * Work.CR.Flat.dbarCoord k W (z + x))
      = Work.CR.Flat.Cauchy.bmGamma n * W z := by
    rw [← hkey]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Work.CR.Flat.Cauchy.dbarCoord_comp_add k
      ((hW.differentiable one_ne_zero).differentiableAt)]
  rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
  simp only [Work.CR.Flat.Cauchy.bmPot]
  exact hmain.symm

end

end Work.NN.Core
