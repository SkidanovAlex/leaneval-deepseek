import Mathlib
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.Topology.Surface.hasSectorBoundary_union_of_two_sublevel

/-!
# The cone condition for a finite union of chart balls in *different* charts

`Work.SimplyConnected.ABS.region_with_sector_boundary` needs, for a region presented as a finite union
of chart balls (the shape the ABS tiling / the engulfing produces), the sector (cone) condition at
every frontier point.  The existing interface `sectorCondition_chartBallUnion_generalPosition` proves
this for balls that are **all round in one chart**, which forces the engulfing region into a single
chart -- i.e. it forces planarity (`NOTES_region_with_sector_boundary_STATUS.md`, §BQ.4 item 1).

This module removes that restriction.  Let `c : ι → OpenPartialHomeomorph X ℂ` be finitely many atlas
charts and `chartBall (c i) (a i) (ρ i)` the corresponding round chart balls, with each closed ball
inside the target of its chart.  Then

`U := ⋃ i, chartBall (c i) (a i) (ρ i)`

satisfies the cone condition at every frontier point, provided

* **general position** (`htwo`): at most two of the *closed* chart balls contain each frontier point,
  and
* **no external tangency** (`hgood`): for two such balls, with `b` the derivative of the transition
  `c j ∘ (c i)⁻¹` at `(c i) p`, the two outward conormals -- the second transported by `b`, i.e.
  `w ↦ inner ℝ ((c j) p - a j) (b w)` -- are not opposite.

The local analysis is the multi-chart two-ball step
`Work.Topology.Surface.hasSectorBoundary_union_of_two_chartBalls` (module
`hasSectorBoundary_union_of_two_sublevel.lean`), which reads the second ball in the chart of the
first and applies the sub-level aggregation engine.  The locality argument (the union agrees near `p`
with the union of the at-most-two balls through it, because every other closed chart ball is compact
hence away from `p`) is the same one used in the single-chart
`sectorCondition_chartBallUnion_generalPosition`.
-/

open Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.Topology.Surface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **The cone condition for a finite union of chart balls in different charts.** -/
theorem sectorCondition_chartBallUnion_multiChart [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] (c : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, c i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (c i).target)
    (htwo : ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)),
      ({i | p ∈ Submission.chartClosedBall (c i) (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)), ∀ i j, i ≠ j →
      p ∈ Submission.chartClosedBall (c i) (a i) (ρ i) →
      p ∈ Submission.chartClosedBall (c j) (a j) (ρ j) →
      ∃ (b : ℂ →L[ℂ] ℂ), b ≠ 0 ∧
        HasFDerivAt (fun ζ : ℂ => c j ((c i).symm ζ)) b ((c i) p) ∧
        ∃ w : ℂ, 0 < inner ℝ ((c i) p - a i) w ∧ 0 < inner ℝ ((c j) p - a j) (b w)) :
    ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)),
      Work.SimplyConnected.ABS.HasSectorBoundary (⋃ i, Submission.chartBall (c i) (a i) (ρ i)) p := by
  classical
  intro p hp
  set U : Set X := ⋃ i, Submission.chartBall (c i) (a i) (ρ i) with hU
  have hUo : IsOpen U :=
    isOpen_iUnion fun i => Submission.chartBall_isOpen (c i) (a i) (ρ i)
  have hpU : p ∉ U := by
    rw [← hUo.interior_eq]
    exact hp.2
  have hclclosed : ∀ i, IsClosed (Submission.chartClosedBall (c i) (a i) (ρ i)) := by
    intro i
    rw [Submission.chartClosedBall_eq_image (hsub i)]
    exact ((isCompact_closedBall (a i) (ρ i)).image_of_continuousOn
      ((c i).continuousOn_symm.mono (hsub i))).isClosed
  have hclosed : IsClosed (⋃ i, Submission.chartClosedBall (c i) (a i) (ρ i)) :=
    isClosed_iUnion_of_finite hclclosed
  have hpcl : p ∈ ⋃ i, Submission.chartClosedBall (c i) (a i) (ρ i) :=
    closure_minimal (fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i,
        Submission.chartBall_subset_chartClosedBall (c i) (a i) (ρ i) hi⟩) hclosed hp.1
  set T : Set ι := {i | p ∈ Submission.chartClosedBall (c i) (a i) (ρ i)} with hTdef
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpcl
    exact ⟨i, hi⟩
  have hTcard : T.ncard ≤ 2 := by
    rw [hTdef]
    exact htwo p hp
  have hcases : T.ncard = 1 ∨ T.ncard = 2 := by
    have hfin : T.Finite := Set.finite_univ.subset (Set.subset_univ T)
    have hpos : 0 < T.ncard := (Set.ncard_pos (s := T) hfin).mpr hTne
    omega
  -- a point of a closed chart ball that is not in the open ball lies on the chart sphere
  have hsphere : ∀ i, p ∈ Submission.chartClosedBall (c i) (a i) (ρ i) →
      ‖c i p - a i‖ = ρ i := by
    intro i hi
    obtain ⟨hpsrc, hple⟩ := Submission.mem_chartClosedBall.mp hi
    have hball : p ∉ Submission.chartBall (c i) (a i) (ρ i) := by
      intro hmem
      exact hpU (Set.mem_iUnion.mpr ⟨i, hmem⟩)
    have hlt : ¬ ‖c i p - a i‖ < ρ i := by
      intro hlt'
      exact hball (Submission.mem_chartBall.mpr ⟨hpsrc, by
        rw [Metric.mem_ball, dist_eq_norm]; exact hlt'⟩)
    have hle : ‖c i p - a i‖ ≤ ρ i := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hple
      exact hple
    exact le_antisymm hle (le_of_not_gt hlt)
  rcases hcases with h1 | h2
  · -- exactly one closed chart ball contains `p`
    obtain ⟨i₀, hi₀⟩ := Set.ncard_eq_one.mp h1
    have hmem : p ∈ Submission.chartClosedBall (c i₀) (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hi₀]; exact Set.mem_singleton i₀
      exact this
    have haway : ∀ i, i ≠ i₀ → p ∉ Submission.chartClosedBall (c i) (a i) (ρ i) := by
      intro i hi hmem'
      have : i ∈ T := hmem'
      rw [hi₀, Set.mem_singleton_iff] at this
      exact hi this
    set V : Set X := (⋃ i : {i // i ≠ i₀}, Submission.chartClosedBall (c i) (a i) (ρ i))ᶜ
      with hVdef
    have hVo : IsOpen V := by
      rw [hVdef]
      exact isOpen_compl_iff.mpr (isClosed_iUnion_of_finite fun i => hclclosed i)
    have hpV : p ∈ V := by
      rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
      rintro ⟨i, hi⟩
      exact haway i i.2 hi
    have heq : U ∩ V = Submission.chartBall (c i₀) (a i₀) (ρ i₀) ∩ V := by
      ext x
      constructor
      · rintro ⟨hxU, hxV⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        have hii : i = i₀ := by
          by_contra hne
          exact hxV (Set.mem_iUnion.mpr ⟨⟨i, hne⟩,
            Submission.chartBall_subset_chartClosedBall (c i) (a i) (ρ i) hi⟩)
        subst hii
        exact ⟨hi, hxV⟩
      · rintro ⟨hx, hxV⟩
        exact ⟨Set.mem_iUnion.mpr ⟨i₀, hx⟩, hxV⟩
    have hpfr : p ∈ frontier (Submission.chartBall (c i₀) (a i₀) (ρ i₀)) := by
      constructor
      · have hsubB : U ∩ V ⊆ Submission.chartBall (c i₀) (a i₀) (ρ i₀) := fun x hx => by
          have hx' : x ∈ Submission.chartBall (c i₀) (a i₀) (ρ i₀) ∩ V := by
            rw [← heq]; exact hx
          exact hx'.1
        have hcl : p ∈ closure (U ∩ V) := by
          rw [mem_closure_iff_nhds]
          intro W hW
          obtain ⟨x, hx⟩ := (mem_closure_iff_nhds.mp hp.1) (W ∩ V)
            (Filter.inter_mem hW (hVo.mem_nhds hpV))
          exact ⟨x, hx.1.1, hx.2, hx.1.2⟩
        exact closure_mono hsubB hcl
      · rw [(Submission.chartBall_isOpen (c i₀) (a i₀) (ρ i₀)).interior_eq]
        intro hmem'
        exact hpU (Set.mem_iUnion.mpr ⟨i₀, hmem'⟩)
    exact Work.SimplyConnected.ABS.hasSectorBoundary_of_inter_eq hVo hpV heq
      (Work.SimplyConnected.ABS.hasSectorBoundary_chartBall (c := c i₀) (hc i₀) (hρ i₀)
        (hsub i₀) p hpfr)
  · -- exactly two closed chart balls contain `p`
    obtain ⟨i₀, i₁, hne, hT⟩ := Set.ncard_eq_two.mp h2
    have hmem₀ : p ∈ Submission.chartClosedBall (c i₀) (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hT]; exact Set.mem_insert i₀ {i₁}
      exact this
    have hmem₁ : p ∈ Submission.chartClosedBall (c i₁) (a i₁) (ρ i₁) := by
      have : i₁ ∈ T := by rw [hT]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton i₁))
      exact this
    have haway : ∀ i, i ≠ i₀ → i ≠ i₁ → p ∉ Submission.chartClosedBall (c i) (a i) (ρ i) := by
      intro i hi₀' hi₁' hmem'
      have : i ∈ T := hmem'
      rw [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h
      · exact hi₀' h
      · exact hi₁' h
    set V : Set X :=
      (⋃ i : {i // i ≠ i₀ ∧ i ≠ i₁}, Submission.chartClosedBall (c i) (a i) (ρ i))ᶜ with hVdef
    have hVo : IsOpen V := by
      rw [hVdef]
      exact isOpen_compl_iff.mpr (isClosed_iUnion_of_finite fun i => hclclosed i)
    have hpV : p ∈ V := by
      rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
      rintro ⟨i, hi⟩
      exact haway i i.2.1 i.2.2 hi
    have heq : U ∩ V = (Submission.chartBall (c i₀) (a i₀) (ρ i₀) ∪
        Submission.chartBall (c i₁) (a i₁) (ρ i₁)) ∩ V := by
      ext x
      constructor
      · rintro ⟨hxU, hxV⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        have hi' : i = i₀ ∨ i = i₁ := by
          by_contra hcon
          push Not at hcon
          exact hxV (Set.mem_iUnion.mpr ⟨⟨i, hcon.1, hcon.2⟩,
            Submission.chartBall_subset_chartClosedBall (c i) (a i) (ρ i) hi⟩)
        rcases hi' with h | h
        · subst h; exact ⟨Or.inl hi, hxV⟩
        · subst h; exact ⟨Or.inr hi, hxV⟩
      · rintro ⟨hx, hxV⟩
        rcases hx with hx | hx
        · exact ⟨Set.mem_iUnion.mpr ⟨i₀, hx⟩, hxV⟩
        · exact ⟨Set.mem_iUnion.mpr ⟨i₁, hx⟩, hxV⟩
    obtain ⟨b, hbne, hb, w, hw₀, hw₁⟩ := hgood p hp i₀ i₁ hne hmem₀ hmem₁
    exact Work.SimplyConnected.ABS.hasSectorBoundary_of_inter_eq hVo hpV heq
      (hasSectorBoundary_union_of_two_chartBalls (c₁ := c i₀) (c₂ := c i₁)
        (hc i₀) (hc i₁) (hρ i₀) (hρ i₁)
        (Submission.mem_chartClosedBall.mp hmem₀).1 (Submission.mem_chartClosedBall.mp hmem₁).1
        (hsphere i₀ hmem₀) (hsphere i₁ hmem₁) hb hbne ⟨w, hw₀, hw₁⟩)

end Work.Topology.Surface
