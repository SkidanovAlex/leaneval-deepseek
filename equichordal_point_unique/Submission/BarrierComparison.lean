import Submission.UnifDeps
import Submission.RiemannSurface
import Submission.SuperharmonicX
import Submission.DirichletLim
import Submission.MaxPrincipleRegion

/-!
# The subharmonic calculus, and the barrier comparison for the region-Perrron envelope

This module fills the two gaps in the subharmonic/superharmonic algebra that the barrier argument of
the region-Dirichlet problem needs:

* `Submission.SubharmonicOnX.add` — the **sum of two subharmonic functions is subharmonic** (and the
  pointwise/chart versions); dually, a subharmonic function minus a superharmonic function is
  subharmonic (`Submission.SubharmonicOnX.sub_superharmonicOnX`).

* `Submission.limEnvelope_le_smul_of_barrier` — **the barrier comparison step**: if `w` is
  superharmonic and nonnegative on a relatively compact open set `U` and the boundary data of the
  limsup Perron family satisfies `f ζ ≤ 0` at every frontier point of `U`, then the Perron envelope
  is bounded by `M · w` on `U`.  In particular, wherever `w` tends to `0` at the boundary, so does
  the envelope: this is the step that lets one produce the region Green function of a chart ball
  (with boundary data `0`) from the barrier `(ρ - ‖c · - a‖)/ρ`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

section Algebra

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The circle mean-value inequality is additive. -/
theorem SubharmonicAtChart.add {u v : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (hu : SubharmonicAtChart u c x) (hv : SubharmonicAtChart v c x) :
    SubharmonicAtChart (fun y => u y + v y) c x := by
  obtain ⟨hxs, ρu, hρu, htu, hcu, hmu⟩ := hu
  obtain ⟨-, ρv, hρv, htv, hcv, hmv⟩ := hv
  refine ⟨hxs, min ρu ρv, lt_min hρu hρv, (Metric.ball_subset_ball (min_le_left _ _)).trans htu,
    ?_, ?_⟩
  · have heq : (fun y : X => u y + v y) ∘ c.symm
        = (u ∘ c.symm) + (v ∘ c.symm) := rfl
    rw [heq]
    exact (hcu.mono (Metric.ball_subset_ball (min_le_left _ _))).add
      (hcv.mono (Metric.ball_subset_ball (min_le_right _ _)))
  · intro p hp r hr hpr
    have hpU : p ∈ Metric.ball (c x) ρu := (Metric.ball_subset_ball (min_le_left _ _)) hp
    have hpV : p ∈ Metric.ball (c x) ρv := (Metric.ball_subset_ball (min_le_right _ _)) hp
    have hsubU : Metric.closedBall p r ⊆ Metric.ball (c x) ρu :=
      hpr.trans (Metric.ball_subset_ball (min_le_left _ _))
    have hsubV : Metric.closedBall p r ⊆ Metric.ball (c x) ρv :=
      hpr.trans (Metric.ball_subset_ball (min_le_right _ _))
    have h1 := hmu p hpU r hr hsubU
    have h2 := hmv p hpV r hr hsubV
    have hint1 : CircleIntegrable (u ∘ c.symm) p r :=
      (hcu.mono (fun z hz => hsubU (Metric.sphere_subset_closedBall hz))).circleIntegrable
        (le_of_lt hr)
    have hint2 : CircleIntegrable (v ∘ c.symm) p r :=
      (hcv.mono (fun z hz => hsubV (Metric.sphere_subset_closedBall hz))).circleIntegrable
        (le_of_lt hr)
    have hadd := Real.circleAverage_add hint1 hint2
    have heq : (fun y : X => u y + v y) ∘ c.symm
        = (u ∘ c.symm) + (v ∘ c.symm) := rfl
    rw [heq, hadd]
    exact add_le_add h1 h2

/-- The reverse circle mean-value inequality is additive. -/
theorem SuperharmonicAtChart.add {u v : X → ℝ} {c : OpenPartialHomeomorph X ℂ} {x : X}
    (hu : SuperharmonicAtChart u c x) (hv : SuperharmonicAtChart v c x) :
    SuperharmonicAtChart (fun y => u y + v y) c x := by
  obtain ⟨hxs, ρu, hρu, htu, hcu, hmu⟩ := hu
  obtain ⟨-, ρv, hρv, htv, hcv, hmv⟩ := hv
  refine ⟨hxs, min ρu ρv, lt_min hρu hρv, (Metric.ball_subset_ball (min_le_left _ _)).trans htu,
    ?_, ?_⟩
  · have heq : (fun y : X => u y + v y) ∘ c.symm
        = (u ∘ c.symm) + (v ∘ c.symm) := rfl
    rw [heq]
    exact (hcu.mono (Metric.ball_subset_ball (min_le_left _ _))).add
      (hcv.mono (Metric.ball_subset_ball (min_le_right _ _)))
  · intro p hp r hr hpr
    have hpU : p ∈ Metric.ball (c x) ρu := (Metric.ball_subset_ball (min_le_left _ _)) hp
    have hpV : p ∈ Metric.ball (c x) ρv := (Metric.ball_subset_ball (min_le_right _ _)) hp
    have hsubU : Metric.closedBall p r ⊆ Metric.ball (c x) ρu :=
      hpr.trans (Metric.ball_subset_ball (min_le_left _ _))
    have hsubV : Metric.closedBall p r ⊆ Metric.ball (c x) ρv :=
      hpr.trans (Metric.ball_subset_ball (min_le_right _ _))
    have h1 := hmu p hpU r hr hsubU
    have h2 := hmv p hpV r hr hsubV
    have hint1 : CircleIntegrable (u ∘ c.symm) p r :=
      (hcu.mono (fun z hz => hsubU (Metric.sphere_subset_closedBall hz))).circleIntegrable
        (le_of_lt hr)
    have hint2 : CircleIntegrable (v ∘ c.symm) p r :=
      (hcv.mono (fun z hz => hsubV (Metric.sphere_subset_closedBall hz))).circleIntegrable
        (le_of_lt hr)
    have hadd := Real.circleAverage_add hint1 hint2
    have heq : (fun y : X => u y + v y) ∘ c.symm
        = (u ∘ c.symm) + (v ∘ c.symm) := rfl
    rw [heq, hadd]
    exact add_le_add h1 h2

/-- The sum of two subharmonic functions is subharmonic at a point. -/
theorem SubharmonicOnXAt.add {u v : X → ℝ} {x : X} (hu : SubharmonicOnXAt u x)
    (hv : SubharmonicOnXAt v x) : SubharmonicOnXAt (fun y => u y + v y) x :=
  SubharmonicAtChart.add hu hv

/-- The sum of two subharmonic functions is subharmonic. -/
theorem SubharmonicOnX.add {u v : X → ℝ} {U : Set X} (hu : SubharmonicOnX u U)
    (hv : SubharmonicOnX v U) : SubharmonicOnX (fun x => u x + v x) U :=
  ⟨hu.1.add hv.1, fun x hx => (hu.2 x hx).add (hv.2 x hx)⟩

/-- **A subharmonic function minus a superharmonic function is subharmonic.** -/
theorem SubharmonicOnX.sub_superharmonicOnX {u v : X → ℝ} {U : Set X} (hu : SubharmonicOnX u U)
    (hv : SuperharmonicOnX v U) : SubharmonicOnX (fun x => u x - v x) U := by
  have hneg : SubharmonicOnX (fun x => -v x) U := hv.neg
  have := hu.add hneg
  simpa [sub_eq_add_neg] using this

end Algebra

section Comparison

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [PreconnectedSpace X]

/-- **The barrier comparison step for the region-Perrron envelope.**  If `W ≥ 0` is superharmonic
on a relatively compact open set `U` and the limsup boundary data `f` is `≤ 0` on the frontier of
`U`, then the Perron envelope is bounded by `W` on `U`. -/
theorem limEnvelope_le_of_superharmonic_bound {U : Set X} (hU : IsOpen U)
    (hcomp : IsCompact (closure U)) (hne0 : (frontier U).Nonempty) {f : X → ℝ} {M : ℝ}
    (hneF : (limFamily U f M).Nonempty) {W : X → ℝ} (hW : SuperharmonicOnX W U)
    (hW0 : ∀ x ∈ U, 0 ≤ W x) (hf0 : ∀ ζ ∈ frontier U, f ζ ≤ 0) :
    ∀ x ∈ U, limEnvelope U f M x ≤ W x := by
  have hmem : ∀ v ∈ limFamily U f M, ∀ x ∈ U, v x ≤ W x := by
    intro v hv
    have hsub : SubharmonicOnX (fun x => v x - W x) U :=
      SubharmonicOnX.sub_superharmonicOnX (limFamily_subharmonic hv) hW
    have hle := SubharmonicOnX.le_of_frontier_limsup hU hsub hcomp hne0 (a := 0) ?_
    · intro x hx
      have := hle x hx
      linarith
    · intro ζ hζ ε hε
      filter_upwards [limFamily_limsup hv hζ hε, self_mem_nhdsWithin] with z hz hzU
      have hz0 : 0 ≤ W z := hW0 z hzU
      have hfζ : f ζ ≤ 0 := hf0 ζ hζ
      show v z - W z ≤ 0 + ε
      linarith
  intro x hx
  rw [limEnvelope, upperEnvelope]
  refine csSup_le ((limFamily_isPerronOn hU hneF).nonempty.image _) ?_
  rintro y ⟨v, hv, rfl⟩
  exact hmem v hv x hx

end Comparison

end Submission
