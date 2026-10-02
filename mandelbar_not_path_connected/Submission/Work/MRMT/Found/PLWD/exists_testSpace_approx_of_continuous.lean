/-
# Test functions approximate continuous compactly supported functions in `L²(ℂ)`

This file proves `Work.MRMT.Found.PLWD.exists_testSpace_approx_of_continuous`: a continuous
function `h : ℂ → ℂ` whose support lies in the closed ball of radius `r` around the origin and
with `r < R` is approximated in `L²(ℂ)` by a *test function* `ψ ∈ Work.MRMT.Found.testSpace R`,
i.e. a `C¹` function whose (topological) support is contained in the open ball `ball 0 R`.

The proof is mollification: `h` is compactly supported and continuous, hence `h ∈ L²(ℂ)`.  For
`ε > 0` the `L²`-continuity of translation of `h`
(`Work.MRMT.QC.existsBumpIntegralMollSubLe`) produces `δ > 0` such that every normalised bump
kernel `ρ` with outer radius `≤ δ` satisfies `∫ ‖ρ ⋆ h - h‖² ≤ ε²`.  Choosing `N` so large that
the bump `Work.MRMT.Weyl.bump N` has outer radius `< min δ (R - r)`, the mollification
`ψ = ρ_N ⋆ h` is `C¹`, compactly supported, supported in `closedBall 0 (rOut N + r) ⊆ ball 0 R`,
and its `L²` distance to `h` is at most `ε`.
-/
import Mathlib
import Submission.Work.MRMT.Found.PLWD.Defs
import Submission.Work.MRMT.QC.existsBumpIntegralMollSubLe
import Submission.Work.MRMT.Found.support_moll_subset

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal Convolution

namespace Work.MRMT.Found.PLWD

/-- A continuous function whose support is contained in a closed ball around the origin is
square integrable for the Lebesgue measure on `ℂ`. -/
lemma memLp_two_of_continuous_support_subset_closedBall {r : ℝ} {h : ℂ → ℂ}
    (hc : Continuous h) (hs : Function.support h ⊆ Metric.closedBall 0 r) :
    MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hcs : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) r) hs
  have hsq : HasCompactSupport (fun z : ℂ => ‖h z‖ ^ 2) :=
    hcs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hint : Integrable (fun z : ℂ => ‖h z‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport hsq
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hint

/-- If the square of the modulus of `f` has integral at most `C ^ 2`, then the `L²`-seminorm of
`f` is at most `C`, for `C ≥ 0`. -/
lemma eLpNorm_two_le_ofReal_of_integral_sq_le {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    {C : ℝ} (hint : Integrable (fun z : ℂ => ‖f z‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hC : 0 ≤ C)
    (h : ∫ z, ‖f z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ C ^ 2) :
    eLpNorm f 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal C := by
  have hof : ENNReal.ofReal (∫ z, ‖f z‖ ^ 2) = ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => sq_nonneg _)
  rw [Work.MRMT.QC.eLpNorm_two_eq_lintegral_ofReal f hf, ← hof]
  refine (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg C) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hC]

theorem exists_testSpace_approx_of_continuous {r R : ℝ} (hrR : r < R) {h : ℂ → ℂ}
    (hc : Continuous h) (hs : Function.support h ⊆ Metric.closedBall 0 r) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Work.MRMT.Found.testSpace R,
      MeasureTheory.eLpNorm (fun z => (ψ : ℂ → ℂ) z - h z) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal ε := by
  have hmem : MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    memLp_two_of_continuous_support_subset_closedBall hc hs
  -- `L²`-continuity of translation: a bound on the mollification defect in terms of the radius.
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.MRMT.QC.existsBumpIntegralMollSubLe hmem (ε := ε ^ 2) (by positivity)
  -- Choose `N` with `rOut (bump N) < min δ (R - r)`.
  have hmin : 0 < min δ (R - r) := lt_min hδpos (by linarith)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (Work.MRMT.Weyl.bump n).rOut < min δ (R - r) :=
    Work.MRMT.Weyl.tendsto_rOut_bump.eventually (Iio_mem_nhds hmin)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hNδ : (Work.MRMT.Weyl.bump N).rOut ≤ δ :=
    le_of_lt ((hN N le_rfl).trans_le (min_le_left _ _))
  have hNR : (Work.MRMT.Weyl.bump N).rOut < R - r :=
    (hN N le_rfl).trans_le (min_le_right _ _)
  obtain ⟨hmem_sub, hbound⟩ := hδ (Work.MRMT.Weyl.bump N) hNδ
  -- The mollified function `ρ_N ⋆ h`.
  have hρsupp : Function.support ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ⊆
      Metric.closedBall 0 (Work.MRMT.Weyl.bump N).rOut := by
    rw [ContDiffBump.support_normed_eq]
    exact Metric.ball_subset_closedBall
  have hsupp : Function.support (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) ⊆
      Metric.closedBall 0 ((Work.MRMT.Weyl.bump N).rOut + r) :=
    Work.MRMT.Found.support_moll_subset hρsupp hs
  have hcd : ContDiff ℝ 1 (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) :=
    Work.MRMT.Weyl.contDiff_moll
      ((Work.MRMT.Weyl.bump N).contDiff_normed
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) (n := 1))
      ((Work.MRMT.Weyl.bump N).hasCompactSupport_normed
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
      hc.locallyIntegrable
  have hcsm : HasCompactSupport (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) ((Work.MRMT.Weyl.bump N).rOut + r)) hsupp
  have htsupp : tsupport (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) ⊆ Metric.ball 0 R := by
    refine (closure_mono hsupp).trans ?_
    rw [Metric.isClosed_closedBall.closure_eq]
    exact Metric.closedBall_subset_ball (by linarith)
  refine ⟨⟨Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h, hcd, hcsm, htsupp⟩, ?_⟩
  show eLpNorm (fun z => Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h z - h z) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal ε
  exact eLpNorm_two_le_ofReal_of_integral_sq_le
    (hcd.continuous.aestronglyMeasurable.sub hc.aestronglyMeasurable)
    ((memLp_two_iff_integrable_sq_norm
      (hcd.continuous.aestronglyMeasurable.sub hc.aestronglyMeasurable)).mp hmem_sub)
    hε.le hbound

end Work.MRMT.Found.PLWD
