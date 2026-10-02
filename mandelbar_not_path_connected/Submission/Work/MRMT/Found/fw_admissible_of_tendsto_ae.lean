import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Set

/-- Given a sequence of smooth coefficients `μn`, each supported in the closed ball of radius
`M`, converging pointwise a.e. to `μ`, with `‖μ‖ ≤ k < 1` a.e., the a.e. representative
`μ' = μ · 1_{B(0,M)}` is admissible, square-integrable, agrees a.e. with `μ`, is supported in
`B(0,M)` (exactly), and is a.e. bounded by `k`.

The point is that each `μn` vanishes outside `B(0,M)`, so its a.e. limit `μ` does too: `μ'` is
obtained from `μ` by forcing the values off the ball to be zero, which changes `μ` only on a null
set.  Membership in `L²` then follows from `HasCompactSupport.memLp_of_bound`, and `k ≥ 0` (used
for the a.e. bound) follows from `‖μ‖ ≤ k` holding on a non-null set. -/
theorem fw_admissible_of_tendsto_ae {μ : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k M : ℝ}
    (hk1 : k < 1)
    (hμnC : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hμnT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z)))
    (hμbd : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ μ' : ℂ → ℂ,
      Work.MRMT.Found.Admissible μ' ∧
      MeasureTheory.MemLp μ' 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) ∧
      μ' =ᵐ[MeasureTheory.volume] μ ∧
      (∀ z : ℂ, M < ‖z‖ → μ' z = 0) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ' z‖ ≤ k) := by
  -- `k` is nonnegative because `‖μ z‖ ≤ k` holds on a set of positive measure.
  have hk0 : 0 ≤ k := by
    by_contra hk
    rw [not_le] at hk
    have hset : {z : ℂ | ¬ (‖μ z‖ ≤ k)} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      exact not_le.mpr (lt_of_lt_of_le hk (norm_nonneg (μ z)))
    have h0 : (MeasureTheory.volume : MeasureTheory.Measure ℂ) Set.univ = 0 := by
      rw [← hset]
      exact MeasureTheory.ae_iff.mp hμbd
    rw [show (MeasureTheory.volume : MeasureTheory.Measure ℂ) Set.univ = ⊤ from by simp] at h0
    exact ENNReal.top_ne_zero h0
  -- `μ` vanishes a.e. outside the ball of radius `M`.
  have hμ_supp : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      z ∉ Metric.closedBall (0:ℂ) M → μ z = 0 := by
    filter_upwards [hμnT] with z hz
    intro hzc
    have hzM : M < ‖z‖ := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hzc
      exact hzc
    have hzero : ∀ n, μn n z = 0 := fun n => by
      by_contra hne
      exact absurd (hμnSp n z hne) (not_le.mpr hzM)
    have hseq : (fun n => μn n z) = fun _ => (0:ℂ) := by funext n; exact hzero n
    have hlim0 : Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds 0) := by
      rw [hseq]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hz hlim0
  -- `μ` is a.e. strongly measurable as an a.e. limit of continuous functions.
  have hμ_meas : AEStronglyMeasurable μ (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => (hμnC n).continuous.aestronglyMeasurable) hμnT
  -- A.e. bound for the truncated coefficient.
  have hμ'bd : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖(Metric.closedBall (0:ℂ) M).indicator μ z‖ ≤ max k 0 := by
    filter_upwards [hμbd] with z hz
    by_cases hzc : z ∈ Metric.closedBall (0:ℂ) M
    · rw [Set.indicator_of_mem hzc]; exact le_trans hz (le_max_left _ _)
    · rw [Set.indicator_of_notMem hzc, norm_zero]; exact le_max_right _ _
  have hμ'meas : AEStronglyMeasurable ((Metric.closedBall (0:ℂ) M).indicator μ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    hμ_meas.indicator (Metric.isClosed_closedBall.measurableSet)
  have hμ'cs : HasCompactSupport ((Metric.closedBall (0:ℂ) M).indicator μ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:ℂ) M)
      (fun x hx => Set.indicator_of_notMem hx μ)
  refine ⟨(Metric.closedBall (0:ℂ) M).indicator μ, ?_, ?_, ?_, ?_, ?_⟩
  · -- admissibility
    refine ⟨hμ'meas, ⟨max k 0, max_lt hk1 (by norm_num), hμ'bd⟩, ?_⟩
    exact Metric.isBounded_closedBall.subset (fun z hz => by
      by_contra hzc
      exact hz (Set.indicator_of_notMem hzc μ))
  · -- square integrability
    exact hμ'cs.memLp_of_bound hμ'meas (max k 0) hμ'bd
  · -- a.e. equality with `μ`
    filter_upwards [hμ_supp] with z hz
    by_cases hzc : z ∈ Metric.closedBall (0:ℂ) M
    · rw [Set.indicator_of_mem hzc]
    · rw [Set.indicator_of_notMem hzc]; exact (hz hzc).symm
  · -- exact support condition
    intro z hz
    have hzc : z ∉ Metric.closedBall (0:ℂ) M := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact not_le.mpr hz
    exact Set.indicator_of_notMem hzc μ
  · -- a.e. bound by `k`
    filter_upwards [hμbd] with z hz
    by_cases hzc : z ∈ Metric.closedBall (0:ℂ) M
    · rw [Set.indicator_of_mem hzc]; exact hz
    · rw [Set.indicator_of_notMem hzc, norm_zero]; exact hk0

end Work.MRMT.Found
