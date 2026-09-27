import Mathlib
import Submission.Work.Drive.sweepTripleGeneric

/-!
# The *pointwise* (and centred) surjectivity of the design's triple — the richness hypothesis

`Work.Drive.hsurj_sweepChartFam` (`sweepTripleGeneric.lean`) proves the parametric Sard's `hsurj`
clause for the design's triple, but its containment hypothesis
`hcontain : ∀ t y, ‖t‖ < ε → y ∈ K → ∀ k, (chain k) (bPartC k y) ∈ (chr p).source` is anchored at the
parameter `0` and at *every* `y ∈ K`.  The localized Sard
(`Work.Drive.localSard`) and the reference-triple genericity consuming it
(`Work.Drive.refTripleLocal`) need the hypothesis at an **arbitrary centre** `t₀` — because that is
what makes the richness hypothesis *inherited* by the translated families `τ ↦ G (t₀ + τ)`.

This file records that the containment is in fact used at the **single point** `(t,y)` under
consideration, so that

* `Work.Drive.hsurj_sweepChartFam_at` — the *pointwise* form, with containment only at the point;
* `Work.Drive.richness_sweepChartFam` — the **centred** form in the exact shape of
  `refTripleLocal`'s hypothesis (one chart `p`, a compact `K`, a centre `t₀`, a radius `δ`),

hold with the *same proof* as `hsurj_sweepChartFam`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {Q : ℂ → CappingSpace}

/-- **The parametric Sard's `hsurj` clause, with the chart containment assumed only at the point
`(t,y)` under consideration.**

This is `Work.Drive.hsurj_sweepChartFam` with the hypothesis
`hcontain : ∀ t y, ‖t‖ < ε → y ∈ K → ∀ k, …` replaced by its value at the single pair `(t,y)`: the
proof of `hsurj_sweepChartFam` never consults the containment anywhere else. -/
theorem hsurj_sweepChartFam_at (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2))
    (p : CappingSpace) (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9))
    (hcontain : ∀ k : Fin 3,
      sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source)
    (hz : Work.Drive.TParity.chartDiff3 p (sweepChartFam P Ξ c t) y = 0) :
    Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
      Work.Drive.TParity.chartDiff3 p (sweepChartFam P Ξ c t') y) t) := by
  classical
  -- ## the meet and the chart containment
  have hsrc : y ∈ Work.Drive.TParity.region3 p (sweepChartFam P Ξ c t) := hcontain
  have hmeet : Work.Drive.TParity.meet3 (sweepChartFam P Ξ c t) y :=
    (Work.Drive.TParity.chartDiff3_eq_zero_iff hsrc).mp hz
  have hval : ∀ k : Fin 3, sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) =
      sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y) := by
    intro k
    fin_cases k
    · rfl
    · exact hmeet.1.symm
    · exact hmeet.2.symm
  have hlev : ∀ k : Fin 3, levelOf (sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y))
      = levelOf (sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y)) :=
    fun k => congrArg levelOf (hval k)
  -- ## the block derivatives
  have hsl : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : EuclideanSpace ℝ (Fin 4) =>
        sweepChartSlice P Ξ c k s (Work.Drive.TParity.bPartC k y)) :=
    fun k => contMDiff_sweepChartSlice_point P Ξ c k y hslice
  have hBsrc : ∀ k : Fin 3,
      sweepChartSlice P Ξ c k (blk k t) (Work.Drive.TParity.bPartC k y) ∈ (chr p).source := by
    intro k
    rw [← sweepChartFam_eq_slice]
    exact hcontain k
  have hDf : ∀ k : Fin 3, HasFDerivAt
      (fun t' => chr p (sweepChartFam P Ξ c t' k (Work.Drive.TParity.bPartC k y)))
      ((sweepBlockDeriv P Ξ c k p t y).comp (blk k)) t := by
    intro k
    have hcomp := (sweepBlockDeriv_hasFDerivAt P Ξ c k p t y (hsl k) (hBsrc k)).comp t
      ((blk k).hasFDerivAt)
    simpa only [Function.comp_def, sweepChartFam_eq_slice] using hcomp
  have hBsurj : ∀ k : Fin 3, y (Work.Drive.bIdx k 2) ≠ 0 →
      Function.Surjective (sweepBlockDeriv P Ξ c k p t y) := by
    intro k hk
    refine surjective_sweepBlockDeriv P Ξ c k p t y (hBsrc k) ?_
    have hyne : (Work.Drive.TParity.bPartC k y) 2 ≠ 0 := by
      rw [Work.Drive.TParity.bPartC_apply]
      exact hk
    change Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
      (fun t' => clampedSweep (c k) (fun s => 1 - s) (fun z => Ξ t' (P k z))
        (Work.Drive.TParity.bPartC k y)) (blk k t))
    exact surjective_mfderiv_clampedSweep_ne_zero (P := P k) hΞ (c k) (hc k)
      (Work.Drive.TParity.bPartC k y) hyne (blk k t)
  -- ## at a floor the level is the truncation level
  have hfloor : ∀ k : Fin 3, y (Work.Drive.bIdx k 2) = 0 →
      levelOf (sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y)) = c k := by
    intro k hk
    have h2 : (Work.Drive.TParity.bPartC k y).ofLp 2 = 0 := by
      rw [Work.Drive.TParity.bPartC_apply]
      exact hk
    rw [sweepChartFam_eq_slice, sweepChartSlice,
      clampedSweep_face_zero (c k) (hc k) (fun r => 1 - r)
        (fun z => Ξ (blk k t) (P k z)) (by norm_num)
        (Work.Drive.TParity.bPartC k y) h2]
    exact levelOf_shadow (c k) (hc k) _
  -- ## at most one chain on its floor
  have hAtMost : ∀ k k' : Fin 3, y (Work.Drive.bIdx k 2) = 0 →
      y (Work.Drive.bIdx k' 2) = 0 → k = k' := by
    intro k k' hk hk'
    refine hcdist k k' ?_
    have h1 : c k = levelOf (sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y)) := by
      rw [← hfloor k hk]; exact hlev k
    have h2 : c k' = levelOf (sweepChartFam P Ξ c t 0 (Work.Drive.TParity.bPartC 0 y)) := by
      rw [← hfloor k' hk']; exact hlev k'
    rw [h1, h2]
  have hfree : ∀ i j l : Fin 3, i ≠ j → i ≠ l →
      Function.Surjective (sweepBlockDeriv P Ξ c i p t y) →
      ∀ z : EuclideanSpace ℝ (Fin 4), ∃ u : EuclideanSpace ℝ (Fin 12),
        ((sweepBlockDeriv P Ξ c i p t y).comp (blk i)) u = z ∧
          ((sweepBlockDeriv P Ξ c j p t y).comp (blk j)) u = 0 ∧
          ((sweepBlockDeriv P Ξ c l p t y).comp (blk l)) u = 0 :=
    fun i j l hij hil hi => pairFree_of_blockSurjective (π := blk)
      (B := fun k => sweepBlockDeriv P Ξ c k p t y)
      (D := fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) (fun k => rfl) blk_join hij hil hi
  -- ## the case analysis on the (at most one) chain on its floor
  by_cases h0 : y (Work.Drive.bIdx 0 2) = 0
  · have h1ne : y (Work.Drive.bIdx 1 2) ≠ 0 :=
      fun h => absurd (hAtMost 0 1 h0 h) (by decide)
    have h2ne : y (Work.Drive.bIdx 2 2) ≠ 0 :=
      fun h => absurd (hAtMost 0 2 h0 h) (by decide)
    refine Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair12 12
      (sweepChartFam P Ξ c) p t y (fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) hDf ?_ ?_
    · exact hfree 1 0 2 (by decide) (by decide) (hBsurj 1 h1ne)
    · exact hfree 2 0 1 (by decide) (by decide) (hBsurj 2 h2ne)
  · by_cases h1 : y (Work.Drive.bIdx 1 2) = 0
    · have h0ne : y (Work.Drive.bIdx 0 2) ≠ 0 := h0
      have h2ne : y (Work.Drive.bIdx 2 2) ≠ 0 :=
        fun h => absurd (hAtMost 1 2 h1 h) (by decide)
      refine Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair02 12
        (sweepChartFam P Ξ c) p t y (fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) hDf ?_ ?_
      · exact hfree 0 1 2 (by decide) (by decide) (hBsurj 0 h0ne)
      · exact hfree 2 0 1 (by decide) (by decide) (hBsurj 2 h2ne)
    · have h0ne : y (Work.Drive.bIdx 0 2) ≠ 0 := h0
      have h1ne : y (Work.Drive.bIdx 1 2) ≠ 0 := h1
      refine Work.Drive.TParity.surjective_fderiv_chartDiff3_of_pair01 12
        (sweepChartFam P Ξ c) p t y (fun k => (sweepBlockDeriv P Ξ c k p t y).comp (blk k)) hDf ?_ ?_
      · exact hfree 0 1 2 (by decide) (by decide) (hBsurj 0 h0ne)
      · exact hfree 1 0 2 (by decide) (by decide) (hBsurj 1 h1ne)

/-- **The centred form of the design's `hsurj` — the richness hypothesis of `refTripleLocal`.**

For *every* chart `p`, compact `K`, centre `t₀` and radius `δ`, if the chart `chr p` contains all three
chain values on the ball `‖t - t₀‖ < δ` and the box `K`, then at every zero `(t,y)` of the charted
triple difference in that region the parameter-derivative is onto.  The containment is used only at
`(t,y)` (`hsurj_sweepChartFam_at`), so the ball is irrelevant to the proof. -/
theorem richness_sweepChartFam (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (hΞ : ChartPert Q 4 Ξ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k)) :
    ∀ (p : CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9)))
      (t₀ : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), IsCompact K → 0 < δ →
      (∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K → ∀ k : Fin 3,
          sweepChartFam P Ξ c t k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (t : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖t - t₀‖ < δ → y ∈ K →
        Work.Drive.TParity.chartDiff3 p (sweepChartFam P Ξ c t) y = 0 →
        Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          Work.Drive.TParity.chartDiff3 p (sweepChartFam P Ξ c t') y) t) := by
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  intro p K t₀ δ _ _ hcont t y ht hy hz
  exact hsurj_sweepChartFam_at P Ξ c hΞ hc hcdist hslice p t y
    (fun k => hcont t y ht hy k) hz

end

end Work.Drive
