import Mathlib
import Submission.Work.MRMT.QC.existsBumpIntegralMollSubLe
import Submission.Work.MRMT.Found.support_moll_subset

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

noncomputable section

/-- For `h ∈ L²(ℂ)` with compact support and every `ε > 0`, some mollification of `h` by a bump
kernel from the sequence `Work.MRMT.Weyl.bump` is `C¹`, compactly supported, in `L²`, and within
`ε` of `h` in the `L²` sense. -/
theorem exists_moll_approx_memLp {h : ℂ → ℂ}
    (hm : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hs : HasCompactSupport h)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      ContDiff ℝ 1 (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) ∧
      HasCompactSupport (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) ∧
      MeasureTheory.MemLp (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) 2 MeasureTheory.volume ∧
      ∫ z, ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump N).normed
        (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h z - h z‖ ^ 2 ≤ ε := by
  obtain ⟨δ, hδpos, hδ⟩ := Work.MRMT.QC.existsBumpIntegralMollSubLe hm hε
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (Work.MRMT.Weyl.bump n).rOut < δ :=
    Work.MRMT.Weyl.tendsto_rOut_bump.eventually (Iio_mem_nhds hδpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hNδ : (Work.MRMT.Weyl.bump N).rOut ≤ δ := le_of_lt (hN N le_rfl)
  obtain ⟨hmem_sub, hbound⟩ := hδ (Work.MRMT.Weyl.bump N) hNδ
  have hli : LocallyIntegrable h (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    hm.locallyIntegrable (by norm_num)
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · exact Work.MRMT.Weyl.contDiff_moll
      ((Work.MRMT.Weyl.bump N).contDiff_normed (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
        (n := 1))
      ((Work.MRMT.Weyl.bump N).hasCompactSupport_normed
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
      hli
  · obtain ⟨R, hR⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hs.isBounded
    have hsupp : Function.support h ⊆ Metric.closedBall 0 R :=
      (subset_tsupport h).trans hR
    have hρsupp : Function.support
        ((Work.MRMT.Weyl.bump N).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ⊆
        Metric.closedBall 0 (Work.MRMT.Weyl.bump N).rOut := by
      rw [ContDiffBump.support_normed_eq]
      exact Metric.ball_subset_closedBall
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 _)
      (support_moll_subset hρsupp hsupp)
  · have haux : MeasureTheory.MemLp (fun z => (Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump N).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h z
        - h z) + h z) 2 MeasureTheory.volume := hmem_sub.add hm
    have heq : (fun z => (Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump N).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h z
        - h z) + h z) =
        (Work.MRMT.Weyl.moll
          ((Work.MRMT.Weyl.bump N).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) h) := by
      funext z; simp
    rwa [heq] at haux
  · exact hbound

end

end Work.MRMT.Found
