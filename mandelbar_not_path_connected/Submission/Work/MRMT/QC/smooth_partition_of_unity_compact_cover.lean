import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open scoped Manifold

/-- Smooth partition of unity subordinate to a finite open cover of a compact subset of `ℂ`:
there are smooth nonnegative compactly supported functions `χ i` with `tsupport (χ i) ⊆ B i`
summing to `1` on a neighbourhood of `K`. -/
theorem smooth_partition_of_unity_compact_cover {K : Set ℂ} (hK : IsCompact K)
    {ι : Type*} [Fintype ι] (B : ι → Set ℂ) (hB : ∀ i, IsOpen (B i)) (hcov : K ⊆ ⋃ i, B i) :
    ∃ χ : ι → ℂ → ℝ, (∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ B i) ∧ (∀ i, ∀ z, 0 ≤ χ i z) ∧
      (∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ W ⊆ ⋃ i, B i ∧ ∀ z ∈ W, ∑ i, χ i z = 1) := by
  classical
  -- Step 1: a compact set `L` with `K ⊆ interior L` and `L ⊆ ⋃ i, B i`.
  have hchoice : ∀ y : {x : ℂ // x ∈ K},
      ∃ i : ι, ∃ r : ℝ, 0 < r ∧ Metric.closedBall y.1 r ⊆ B i := by
    intro y
    rcases Set.mem_iUnion.mp (hcov y.2) with ⟨i, hi⟩
    rcases Metric.isOpen_iff.mp (hB i) y.1 hi with ⟨r, hr, hsub⟩
    exact ⟨i, r / 2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
  choose I R hRpos hRsub using hchoice
  have hcoverK : K ⊆ ⋃ y : {x : ℂ // x ∈ K}, Metric.ball y.1 (R y) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hRpos ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : {x : ℂ // x ∈ K} => Metric.ball y.1 (R y))
      (fun _ => Metric.isOpen_ball) hcoverK
  set L : Set ℂ := ⋃ y ∈ t, Metric.closedBall y.1 (R y) with hLdef
  have hLcomp : IsCompact L := by
    rw [hLdef]
    exact t.finite_toSet.isCompact_biUnion (fun y _ => isCompact_closedBall y.1 (R y))
  have hKint : K ⊆ interior L := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht hx) with ⟨y, hyt, hxy⟩
    refine interior_maximal ?_ Metric.isOpen_ball hxy
    intro z hz
    rw [hLdef]
    exact Set.mem_iUnion₂.mpr ⟨y, hyt, Metric.ball_subset_closedBall hz⟩
  have hLsub : L ⊆ ⋃ i, B i := by
    intro z hz
    rw [hLdef] at hz
    rcases Set.mem_iUnion₂.mp hz with ⟨y, _, hzy⟩
    exact Set.mem_iUnion.mpr ⟨I y, hRsub y hzy⟩
  -- Step 2: a bounded (relatively compact) open refinement of the cover.
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, L ⊆ Metric.ball 0 R0 := by
    rcases (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hLcomp.isBounded with ⟨r, hr⟩
    exact ⟨r, hr⟩
  set U : ι → Set ℂ := fun i => B i ∩ Metric.ball 0 R0 with hUdef
  have hUo : ∀ i, IsOpen (U i) := fun i => (hB i).inter Metric.isOpen_ball
  have hLcov : L ⊆ ⋃ i, U i := by
    intro z hz
    rcases Set.mem_iUnion.mp (hLsub hz) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi, hR0 hz⟩
  -- Step 3: a smooth partition of unity on the closed set `L`, subordinate to `U`.
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℂ)) hLcomp.isClosed U hUo hLcov
  -- Step 4: assemble the answer.
  refine ⟨fun i => (f i : ℂ → ℝ), ?_, ?_, ?_, ?_, interior L, isOpen_interior, hKint, ?_, ?_⟩
  · intro i
    exact ((f i).contMDiff).contDiff
  · intro i
    rw [HasCompactSupport]
    refine (isCompact_closedBall (0 : ℂ) R0).of_isClosed_subset (isClosed_tsupport _) ?_
    intro z hz
    have hz' : z ∈ U i := hf i hz
    rw [hUdef] at hz'
    exact Metric.ball_subset_closedBall hz'.2
  · intro i
    refine (hf i).trans ?_
    intro z hz
    rw [hUdef] at hz
    exact hz.1
  · intro i z
    exact f.nonneg i z
  · exact interior_subset.trans hLsub
  · intro z hz
    have hzL : z ∈ L := interior_subset hz
    have h1 := f.sum_eq_one hzL
    rw [finsum_eq_sum_of_fintype] at h1
    exact h1

end Work.MRMT.QC
