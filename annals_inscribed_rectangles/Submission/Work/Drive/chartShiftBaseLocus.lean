import Mathlib
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.exists_chart_cover

/-!
# The base-locus input of the chart-shift family: `hbase` discharged

The parametrised-Sard route to the engine's hypotheses ends in
`Work.Drive.exists_meet3Hyp_chartShiftClamped_of_ball` (in `chartShiftHsurj.lean`), which needs, besides
the smooth/seam/ball data of the base datum `A`, a compact `K` and two conditions on it:

* `hbase` — the base triple locus of the clamped chart-shift family lies in `interior K`;
* `hbase_ball` — the base charted values on `K` lie in `closedBall c r'`.

This file **constructs `K`** and derives both conditions from the single hypothesis `hloc`, which
constrains the base datum only at the base triple locus:

* `Work.Drive.ChartBall` / `Work.Drive.ChartBallOpen` / `Work.Drive.chartBallSet` — the chart-ball
  condition and the locus `K₀ = {y | ∀ k, A k (bPartC k y) ∈ closedBall c r'}`;
* `Work.Drive.isClosed_chartBallSet`, `isOpen_chartBallOpenSet`,
  `chartBallOpen_subset_chartBall`, `isCompact_chartBallSet_inter`,
  `subset_interior_chartBallSet` — `K := chartBallSet A c r' ∩ closedBall 0 4` is compact, and
  `{y | ∀ k, A k (bPartC k y) ∈ ball c r'} ∩ ball 0 4 ⊆ interior K`;
* **`Work.Drive.exists_meet3Hyp_chartShiftClamped_of_baseLocus`** — the endpoint with `K` and both
  conditions constructed: from `A` (smooth, seam-invariant), the chain of balls
  `ball c r' ⊆ closedBall c r' ⊆ … ⊆ closedBall c r₂ ⊆ (chr p).target` and `hloc`, one gets
  `∀ ε' > 0, ∃ t, ‖t‖ < ε' ∧ Meet3Hyp M (chartShiftClamped p (clampFun …) A t)`;
* **`Work.Drive.exists_meet3Hyp_chartShiftClamped_of_boxBall`** — the clean sufficient condition for
  `hloc`: the base charted values on the **whole** box lie in `closedBall c r''` with `r'' < r₁` (i.e.
  the chosen datum `A` is chart-resident on the box, which is a free choice since `A` is a datum, not
  the design's curve).

The only hypotheses left are thus the *choices* (a smooth seam-invariant datum `A`, balls inside the
chart target) and one containment about `A`; see `CHART_SHIFT_HSURJ_STATUS.md` §8 for the reading of
these in the design's terms, and for the caveat that the conclusion is non-vacuous exactly when the
*base* configuration is (`Meet3Hyp` is a conditional statement about the triple locus).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The chart-ball condition** of a base datum `A`: all three charted values at a box point lie in
`closedBall c r`. -/
def ChartBall (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (y : EuclideanSpace ℝ (Fin 9)) : Prop :=
  ∀ k : Fin 3, A k (TParity.bPartC k y) ∈ Metric.closedBall c r

/-- **The chart-open condition**: the same with the open ball. -/
def ChartBallOpen (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (y : EuclideanSpace ℝ (Fin 9)) : Prop :=
  ∀ k : Fin 3, A k (TParity.bPartC k y) ∈ Metric.ball c r

/-- The chart-ball locus as a set (the compact candidate for `K`). -/
def chartBallSet (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {y | ChartBall A c r y}

theorem chartBall_iff {A c r y} :
    y ∈ chartBallSet A c r ↔ ChartBall A c r y := Iff.rfl

lemma isClosed_chartBallSet (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (hA : ∀ k, Continuous (A k)) :
    IsClosed (chartBallSet A c r) := by
  have h : chartBallSet A c r
      = ⋂ k : Fin 3, {y : EuclideanSpace ℝ (Fin 9) |
          A k (TParity.bPartC k y) ∈ Metric.closedBall c r} := by
    ext y
    simp only [chartBallSet, ChartBall, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter (fun k =>
    IsClosed.preimage ((hA k).comp (TParity.bPartC k).continuous) Metric.isClosed_closedBall)

lemma isOpen_chartBallOpenSet (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (hA : ∀ k, Continuous (A k)) :
    IsOpen {y : EuclideanSpace ℝ (Fin 9) | ChartBallOpen A c r y} := by
  have h : {y : EuclideanSpace ℝ (Fin 9) | ChartBallOpen A c r y}
      = ⋂ k : Fin 3, {y : EuclideanSpace ℝ (Fin 9) |
          A k (TParity.bPartC k y) ∈ Metric.ball c r} := by
    ext y
    simp only [ChartBallOpen, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite (fun k =>
    Metric.isOpen_ball.preimage ((hA k).comp (TParity.bPartC k).continuous))

lemma chartBallOpen_subset_chartBall (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) {r r' : ℝ} (hr : r ≤ r') :
    {y : EuclideanSpace ℝ (Fin 9) | ChartBallOpen A c r y}
      ⊆ {y : EuclideanSpace ℝ (Fin 9) | ChartBall A c r' y} := by
  intro y hy k
  exact Metric.closedBall_subset_closedBall hr (Metric.ball_subset_closedBall (hy k))

lemma isCompact_chartBallSet_inter (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (hA : ∀ k, Continuous (A k)) :
    IsCompact (chartBallSet A c r ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 9)) 4) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall _ 4)
    ((isClosed_chartBallSet A c r hA).inter Metric.isClosed_closedBall)
    Set.inter_subset_right

lemma subset_interior_chartBallSet (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (c : EuclideanSpace ℝ (Fin 4)) {r r'' : ℝ} (hr : r'' ≤ r) (hA : ∀ k, Continuous (A k)) :
    ({y : EuclideanSpace ℝ (Fin 9) | ChartBallOpen A c r'' y} ∩
        Metric.ball (0 : EuclideanSpace ℝ (Fin 9)) 4)
      ⊆ interior (chartBallSet A c r ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 9)) 4) := by
  refine interior_maximal ?_ ?_
  · exact Set.inter_subset_inter (chartBallOpen_subset_chartBall A c hr) Metric.ball_subset_closedBall
  · exact (isOpen_chartBallOpenSet A c r'' hA).inter Metric.isOpen_ball

/-- **The design-facing endpoint: `hbase` from a condition on the base triple locus alone.**

`Work.Drive.exists_meet3Hyp_chartShiftClamped_of_ball` asks for a compact `K` and two conditions on it
(`hbase`: the base triple locus inside `interior K`; `hbase_ball`: the base charted values on `K` in a
closed ball).  Here `K` is **constructed** — `K = chartBallSet A c r' ∩ closedBall 0 4` — and both
conditions are derived from the single hypothesis `hloc`, which constrains the base datum only at the
base triple locus of the clamped chart-shift family (`G 0 = (chr p).symm ∘ clampFun ∘ A`): the charted
values there lie in the *open* ball `ball c r'`.  The inner-ball condition `hroom` is derived as well
(`|blk k t| ≤ ‖t‖`), so this is the parametrised Sard route's complete input list. -/
theorem exists_meet3Hyp_chartShiftClamped_of_baseLocus (p : M)
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hA : ∀ k, ContDiff ℝ Ctop (A k))
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ r' : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hr' : r' < r₁)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (chr p).target)
    (hloc : ∀ y ∈ Submission.Drive.unitBox 8,
      TParity.meet3 (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A 0) y →
      ∀ k : Fin 3, A k (TParity.bPartC k y) ∈ Metric.ball c r') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A t) := by
  have hcont : ∀ k : Fin 3, Continuous (A k) := fun k => (hA k).continuous
  set K : Set (EuclideanSpace ℝ (Fin 9)) :=
    chartBallSet A c r' ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 9)) 4 with hKdef
  have hK : IsCompact K := isCompact_chartBallSet_inter A c r' hcont
  have hbb : ∀ y ∈ K, ∀ k : Fin 3, A k (TParity.bPartC k y) ∈ Metric.closedBall c r' :=
    fun y hy k => hy.1 k
  have hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      TParity.meet3 (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A 0) y →
      y ∈ interior K := by
    intro y hy hmeet
    have hyK : y ∈ {z : EuclideanSpace ℝ (Fin 9) | ChartBallOpen A c r' z} ∩
        Metric.ball (0 : EuclideanSpace ℝ (Fin 9)) 4 := by
      refine ⟨fun k => hloc y hy hmeet k, ?_⟩
      rw [Metric.mem_ball]
      have hle : ‖y‖ ≤ Real.sqrt ((8 : ℝ) + 1) := norm_le_sqrt_of_mem_unitBox hy
      have hlt : Real.sqrt ((8 : ℝ) + 1) < 4 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)]
        norm_num
      simpa using lt_of_le_of_lt hle hlt
    exact subset_interior_chartBallSet A c le_rfl hcont hyK
  exact exists_meet3Hyp_chartShiftClamped_of_ball p A hA hAseam c h1 h12 htarget K hK hbase
    (by linarith : (0 : ℝ) < (r₁ - r') / 2)
    (hroom_of_base_ball A c K hbb (by linarith) le_rfl)

/-- **The clean sufficient condition for `hloc`: a chart-resident base datum.**

If the base datum's charted values on the whole box lie in `closedBall c r''` with `r'' < r₁`, then the
`hloc` hypothesis of `Work.Drive.exists_meet3Hyp_chartShiftClamped_of_baseLocus` holds — no condition on
the base triple locus is needed at all.  This is the form in which a design which *chooses* the datum
`A` chart-resident (the free choice) discharges the input. -/
theorem exists_meet3Hyp_chartShiftClamped_of_boxBall (p : M)
    (A : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hA : ∀ k, ContDiff ℝ Ctop (A k))
    (hAseam : ∀ k x, Work.Drive.onSeam x → A k (Work.Drive.seamInv x) = A k x)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ r'' : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hr'' : r'' < r₁)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (chr p).target)
    (hbox : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      A k (TParity.bPartC k y) ∈ Metric.closedBall c r'') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12) A t) := by
  refine exists_meet3Hyp_chartShiftClamped_of_baseLocus p A hA hAseam c h1 h12
    (r' := (r'' + r₁) / 2) ?_ htarget ?_
  · linarith
  · intro y hy _ k
    refine Metric.mem_ball.mpr ?_
    have h := Metric.mem_closedBall.mp (hbox y hy k)
    linarith

/-! ## The base of the family is the design's own chain

The point of feeding the **charted** datum `A k = (chr p) ∘ P k` into the chart-shift family is that its
`t = 0` slice is exactly `P k` (not merely a charted surrogate): the clamp is the identity on the inner
ball and `(chr p).symm ∘ (chr p)` is the identity on the chart's source.  So the family is a genuine
perturbation of the design's own chain, and the bordism machinery can compare the generic parameter with
the design's sweeps. -/

/-- **The chart-shift family of a charted datum is, at `t = 0`, the datum itself.** -/
theorem chartShiftClamped_charted_zero (p : M) (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂)
    (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3))
    (hsrc : P k x ∈ (chr p).source)
    (hball : (chr p) (P k x) ∈ Metric.ball c r₁) :
    chartShiftClamped p (clampFun c r₁ r₂ h1 h12) (fun j x' => (chr p) (P j x')) 0 k x = P k x := by
  rw [chartShiftClamped, map_zero, add_zero, clampFun_eq_self c r₁ r₂ h1 h12 hball]
  exact (chr p).left_inv hsrc

/-- **The base identification for an arbitrary clamp.**  If `ψ` fixes the charted value `(chr p) (P k x)`
(and lands in the chart's target, so that the family is well defined), then the `t = 0` slice of the
chart-shift family of the charted datum `(chr p) ∘ P` is `P` itself at `x` — the general form of
`Work.Drive.chartShiftClamped_charted_zero`, with the ball replaced by the pointwise hypothesis `hid`. -/
theorem chartShiftClamped_charted_zero_of_localId (p : M) (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (ψ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3))
    (hsrc : P k x ∈ (chr p).source)
    (hid : ψ ((chr p) (P k x)) = (chr p) (P k x)) :
    chartShiftClamped p ψ (fun j x' => (chr p) (P j x')) 0 k x = P k x := by
  rw [chartShiftClamped, map_zero, add_zero, hid]
  exact (chr p).left_inv hsrc

/-- **The one-shot endpoint for the design's own chain.**  Let `P` be a smooth, seam-invariant family of
`3`-chains in the chart at `p`, whose charted values on the box lie in `closedBall c r''`
(`r'' < r₁ < r₂`, `closedBall c r₂ ⊆ (chr p).target`).  Then the clamped chart-shift family of the
**charted** datum `A k = (chr p) ∘ P k` has, for every `ε' > 0`, a parameter `t` with `‖t‖ < ε'` and
`Meet3Hyp M (G t)` — i.e. the engine's hypotheses for a generic perturbation of the design's own chain —
and, for every `t`, its `t = 0` slice is `P` itself on the box.

The only geometric input is `hbox`: the design's chain is *chart-resident on the box* and bounded there
(i.e. its charted values avoid the boundary of the chart); that hypothesis is in turn a compactness
consequence of the continuity of `(chr p) ∘ P k` on the compact box
(`Work.Drive.exists_closedBall_charted_box`). -/
theorem exists_meet3Hyp_chartShiftCharted_of_boxBall (p : M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → P k (Work.Drive.seamInv x) = P k x)
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (chr p).source)
    (c : EuclideanSpace ℝ (Fin 4)) {r₁ r₂ r'' : ℝ} (h1 : 0 < r₁) (h12 : r₁ < r₂) (hr'' : r'' < r₁)
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (chr p).target)
    (hbox : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (chr p) (P k (TParity.bPartC k y)) ∈ Metric.closedBall c r'') :
    ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
        (fun j x' => (chr p) (P j x')) t) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9)), y ∈ Submission.Drive.unitBox 8 →
        chartShiftClamped p (clampFun c r₁ r₂ h1 h12) (fun j x' => (chr p) (P j x'))
          0 k (TParity.bPartC k y) = P k (TParity.bPartC k y)) := by
  have hchart : ContMDiffOn (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop ((chr p : M → _))
      (chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
    simpa [Work.Drive.chr] using h
  have hA : ∀ k : Fin 3, ContDiff ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 3) => (chr p) (P k x)) := by
    intro k
    have hcomp : ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop
        (fun x : EuclideanSpace ℝ (Fin 3) => (chr p) (P k x)) := by
      rw [← contMDiffOn_univ]
      exact hchart.comp (hP k).contMDiffOn (fun x _ => hsrc k x)
    exact (contMDiff_iff_contDiff (𝕜 := ℝ) (n := Ctop)).mp hcomp
  have hAseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), Work.Drive.onSeam x →
      (fun j x' => (chr p) (P j x')) k (Work.Drive.seamInv x)
        = (fun j x' => (chr p) (P j x')) k x :=
    fun k x hx => by
      show (chr p) (P k (Work.Drive.seamInv x)) = (chr p) (P k x)
      rw [hPseam k x hx]
  intro ε' hε'
  obtain ⟨t, ht, hM⟩ := exists_meet3Hyp_chartShiftClamped_of_boxBall p
    (fun j x' => (chr p) (P j x')) hA hAseam c h1 h12 hr'' htarget hbox ε' hε'
  refine ⟨t, ht, hM, fun k y hy => ?_⟩
  refine chartShiftClamped_charted_zero p P c h1 h12 k _ (hsrc k _) ?_
  have h := Metric.mem_closedBall.mp (hbox y hy k)
  exact Metric.mem_ball.mpr (lt_of_le_of_lt h hr'')

/-- **A strict bound from an open ball.** -/
lemma exists_lt_bound_chartBall (p : M) (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (c : EuclideanSpace ℝ (Fin 4)) {r₂ : ℝ}
    (hP : ∀ k : Fin 3, Continuous (P k))
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (chr p).source)
    (hball : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (chr p) (P k (TParity.bPartC k y)) ∈ Metric.ball c r₂) :
    ∃ r'' : ℝ, r'' < r₂ ∧ ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (chr p) (P k (TParity.bPartC k y)) ∈ Metric.closedBall c r'' := by
  have hcont : ∀ k : Fin 3, Continuous (fun y : EuclideanSpace ℝ (Fin 9) =>
      dist ((chr p) (P k (TParity.bPartC k y))) c) := fun k =>
    (((chr p).continuousOn.comp_continuous (hP k) (fun x => hsrc k x)).comp
      (TParity.bPartC k).continuous).dist continuous_const
  have hne : (Submission.Drive.unitBox 8 : Set (EuclideanSpace ℝ (Fin 9))).Nonempty :=
    ⟨0, fun i => by norm_num⟩
  choose y hy hmax using fun k : Fin 3 =>
    (isCompact_unitBox 8).exists_isMaxOn hne (hcont k).continuousOn
  set m : Fin 3 → ℝ := fun k => dist ((chr p) (P k (TParity.bPartC k (y k)))) c with hm
  have hm_lt : ∀ k : Fin 3, m k < r₂ := fun k => Metric.mem_ball.mp (hball (y k) (hy k) k)
  refine ⟨Finset.univ.sup' Finset.univ_nonempty m, ?_, ?_⟩
  · rw [Finset.sup'_lt_iff]
    intro k _
    exact hm_lt k
  · intro y' hy' k
    rw [Metric.mem_closedBall]
    have h1 : dist ((chr p) (P k (TParity.bPartC k y'))) c ≤ m k :=
      (isMaxOn_iff.mp (hmax k)) y' hy'
    have h2 : m k ≤ Finset.univ.sup' Finset.univ_nonempty m :=
      Finset.le_sup' m (Finset.mem_univ k)
    linarith

/-- **The endpoint with a single ball condition.**  The design provides a ball `closedBall c r₂` inside
the chart's target together with the condition that the *charted* chain values on the box lie in the
**open** ball `ball c r₂`; the inner radii are then produced.  This is the cleanest form of the input
list: no radius ordering and no separate boundedness hypothesis is left to the design. -/
theorem exists_meet3Hyp_chartShiftCharted_of_ball (p : M)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → P k (Work.Drive.seamInv x) = P k x)
    (hsrc : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), P k x ∈ (chr p).source)
    (c : EuclideanSpace ℝ (Fin 4)) {r₂ : ℝ}
    (htarget : ∀ u ∈ Metric.closedBall c r₂, u ∈ (chr p).target)
    (hball : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (chr p) (P k (TParity.bPartC k y)) ∈ Metric.ball c r₂) :
    ∃ (r₁ : ℝ) (h1 : 0 < r₁) (h12 : r₁ < r₂),
      ∀ ε' : ℝ, 0 < ε' → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp M (chartShiftClamped p (clampFun c r₁ r₂ h1 h12)
          (fun j x' => (chr p) (P j x')) t) ∧
        (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 9)), y ∈ Submission.Drive.unitBox 8 →
          chartShiftClamped p (clampFun c r₁ r₂ h1 h12) (fun j x' => (chr p) (P j x'))
            0 k (TParity.bPartC k y) = P k (TParity.bPartC k y)) := by
  obtain ⟨r'', hr'', hbound⟩ := exists_lt_bound_chartBall p P c (fun k => (hP k).continuous) hsrc hball
  have hzero : (0 : EuclideanSpace ℝ (Fin 9)) ∈ Submission.Drive.unitBox 8 := fun i => by norm_num
  have hr₂ : 0 < r₂ := by
    have h := Metric.mem_ball.mp (hball 0 hzero 0)
    linarith [dist_nonneg (x := (chr p) (P 0 (TParity.bPartC 0 (0 : EuclideanSpace ℝ (Fin 9)))))
      (y := c)]
  have hr''nn : 0 ≤ r'' := by
    have h := Metric.mem_closedBall.mp (hbound 0 hzero 0)
    linarith [dist_nonneg (x := (chr p) (P 0 (TParity.bPartC 0 (0 : EuclideanSpace ℝ (Fin 9)))))
      (y := c)]
  refine ⟨(r'' + r₂) / 2, by linarith, by linarith, fun ε' hε' => ?_⟩
  have hbox : ∀ y ∈ Submission.Drive.unitBox 8, ∀ k : Fin 3,
      (chr p) (P k (TParity.bPartC k y)) ∈ Metric.closedBall c r'' := hbound
  exact exists_meet3Hyp_chartShiftCharted_of_boxBall p P hP hPseam hsrc c
    (r₁ := (r'' + r₂) / 2) (r'' := r'') (by linarith) (by linarith) (by linarith) htarget hbox ε' hε'

end

end Work.Drive
