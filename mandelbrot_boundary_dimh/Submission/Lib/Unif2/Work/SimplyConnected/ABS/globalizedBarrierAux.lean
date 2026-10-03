import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg

/-!
# Elementary closure properties of superharmonic functions

This module collects the elementary closure properties of `Submission.SuperharmonicOnX` that the
barrier constructions of the uniformization development use.

* `superharmonicOnX_const_dev` — constants are superharmonic.
* `SuperharmonicOnX.inf_const_dev` — **the clamp lemma**: the pointwise minimum of a superharmonic
  function with a constant is superharmonic.  The point is that `Submission.SuperharmonicAtChart`
  requires the circle mean-value inequality at *every* point of the chart ball, not only at its
  centre, so that the inequality for `u ⊓ c` at a centre `p` follows by combining the inequality
  for `u` at `p` with the pointwise bounds `u ⊓ c ≤ u` and `u ⊓ c ≤ c`.
* `superharmonicOnX_of_isOpen_cover_dev` — superharmonicity is local: a function that is
  superharmonic on the members of an open cover is superharmonic on the union.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A constant function is superharmonic on any set. -/
theorem superharmonicOnX_const_dev (k : ℝ) (U : Set X) :
    Submission.SuperharmonicOnX (fun _ : X => k) U := by
  refine ⟨continuousOn_const, fun x _ => ?_⟩
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart]
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  refine ⟨hxsrc, ρ, hρ, hρsub, continuousOn_const, ?_⟩
  intro pp hp r hr hpr
  have h1 : ((fun _ : X => k) ∘ (chartAt ℂ x).symm) = fun _ : ℂ => k := rfl
  rw [h1, Real.circleAverage_const]

/-- **The clamp lemma.**  The pointwise minimum of a superharmonic function with a constant is
superharmonic. -/
theorem SuperharmonicOnX.inf_const_dev {u : X → ℝ} {U : Set X}
    (hu : Submission.SuperharmonicOnX u U) (c : ℝ) :
    Submission.SuperharmonicOnX (fun x => u x ⊓ c) U := by
  refine ⟨hu.1.inf continuousOn_const, fun x hx => ?_⟩
  rw [Submission.SuperharmonicOnXAt, Submission.SuperharmonicAtChart]
  obtain ⟨hxsrc, ρ, hρ, hρsub, hcont, hmvp⟩ := hu.2 x hx
  refine ⟨hxsrc, ρ, hρ, hρsub, hcont.inf continuousOn_const, ?_⟩
  intro pp hp r hr hpr
  have hclose : Metric.sphere pp |r| ⊆ Metric.ball ((chartAt ℂ x) x) ρ := by
    intro z hz
    refine hpr ?_
    have hmem := Metric.sphere_subset_closedBall hz
    rwa [abs_of_pos hr] at hmem
  have hcont_f : ContinuousOn (u ∘ (chartAt ℂ x).symm) (Metric.sphere pp |r|) := hcont.mono hclose
  have hcont_g : ContinuousOn (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) z ⊓ c)
      (Metric.sphere pp |r|) := hcont_f.inf continuousOn_const
  have hint_f : CircleIntegrable (u ∘ (chartAt ℂ x).symm) pp r := hcont_f.circleIntegrable'
  have hint_g : CircleIntegrable (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) z ⊓ c) pp r :=
    hcont_g.circleIntegrable'
  have hfun : (fun y : X => u y ⊓ c) ∘ (chartAt ℂ x).symm
      = fun z : ℂ => (u ∘ (chartAt ℂ x).symm) z ⊓ c := rfl
  rw [hfun]
  have h1 : Real.circleAverage (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) z ⊓ c) pp r
      ≤ Real.circleAverage (u ∘ (chartAt ℂ x).symm) pp r :=
    Real.circleAverage_mono hint_g hint_f (fun z _ => inf_le_left)
  have h2 : Real.circleAverage (fun z : ℂ => (u ∘ (chartAt ℂ x).symm) z ⊓ c) pp r ≤ c :=
    Real.circleAverage_mono_on_of_le_circle hint_g (fun z _ => inf_le_right)
  have h3 : Real.circleAverage (u ∘ (chartAt ℂ x).symm) pp r ≤ (u ∘ (chartAt ℂ x).symm) pp :=
    hmvp pp hp r hr hpr
  exact le_inf (le_trans h1 h3) h2

/-- Superharmonicity is local: a function that is superharmonic on the members of an open cover is
superharmonic on their union. -/
theorem superharmonicOnX_of_isOpen_cover_dev {u : X → ℝ} {U : Set X} {ι : Type*}
    {V : ι → Set X} (hVo : ∀ i, IsOpen (V i)) (hcov : U ⊆ ⋃ i, V i)
    (hV : ∀ i, Submission.SuperharmonicOnX u (V i)) :
    Submission.SuperharmonicOnX u U := by
  constructor
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact ((hV i).1.continuousAt ((hVo i).mem_nhds hxi)).continuousWithinAt
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact (hV i).2 x hxi

end Work.SimplyConnected.ABS
