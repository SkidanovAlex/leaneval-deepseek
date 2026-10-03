import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Commons.Analysis.Complex.Dirichlet.dirichlet_ball
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le

/-!
# The Dirichlet problem on a chart disc of a Riemann surface

Given a chart `c` and a Euclidean disc `Metric.closedBall a ρ ⊆ c.target`, the Dirichlet problem on
the chart disc `chartBall c a ρ` is solved by pulling back the Euclidean solution across `c`.  This
module records the `X`-level statement: continuous boundary data on the chart sphere extend to a
function continuous up to the closed chart disc whose `c`-pullback is harmonic inside.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section ChartSphere

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The `c`-preimage of the Euclidean sphere: the "boundary circle" of the chart disc. -/
def chartSphere (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : Set X :=
  c.source ∩ c ⁻¹' Metric.sphere a ρ

theorem mem_chartSphere {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {x : X} :
    x ∈ chartSphere c a ρ ↔ x ∈ c.source ∧ c x ∈ Metric.sphere a ρ := Iff.rfl

theorem chartSphere_subset_chartClosedBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    chartSphere c a ρ ⊆ chartClosedBall c a ρ :=
  fun _ hx => ⟨hx.1, Metric.sphere_subset_closedBall hx.2⟩

theorem chartSphere_subset_source (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    chartSphere c a ρ ⊆ c.source := inter_subset_left

/-- The chart sphere is the boundary of the chart ball inside the closed chart disc. -/
theorem chartClosedBall_diff_chartBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    chartClosedBall c a ρ \ chartBall c a ρ = chartSphere c a ρ := by
  ext x
  constructor
  · rintro ⟨⟨hxs, hxc⟩, hxnb⟩
    refine ⟨hxs, ?_⟩
    have h1 : ¬ c x ∈ Metric.ball a ρ := fun h => hxnb ⟨hxs, h⟩
    simp only [Set.mem_preimage] at hxc
    rw [Metric.mem_closedBall] at hxc
    rw [Metric.mem_ball] at h1
    change c x ∈ Metric.sphere a ρ
    rw [Metric.mem_sphere]
    exact le_antisymm hxc (not_lt.mp h1)
  · rintro ⟨hxs, hxc⟩
    refine ⟨⟨hxs, Metric.sphere_subset_closedBall hxc⟩, ?_⟩
    intro hb
    have h1 : c x ∈ Metric.ball a ρ := hb.2
    simp only [Set.mem_preimage] at hxc
    rw [Metric.mem_sphere] at hxc
    rw [Metric.mem_ball] at h1
    linarith

end ChartSphere

section Dirichlet

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Dirichlet problem on a chart disc.**  Let `Metric.closedBall a ρ ⊆ c.target` and let `F` be
continuous on the sphere `Metric.sphere a ρ`.  Then there is a function `U : X → ℝ`, continuous on
the closed chart disc, whose `c`-pullback is harmonic on the open ball `Metric.ball a ρ`, and which
equals `F ∘ c` on the chart sphere. -/
theorem exists_dirichletOnChartBall {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) {F : ℂ → ℝ}
    (hF : ContinuousOn F (Metric.sphere a ρ)) :
    ∃ U : X → ℝ,
      (∀ x ∈ chartBall c a ρ, InnerProductSpace.HarmonicAt (U ∘ c.symm) (c x)) ∧
      ContinuousOn U (chartClosedBall c a ρ) ∧
      (∀ x ∈ chartSphere c a ρ, U x = F (c x)) := by
  obtain ⟨u, hu, hG⟩ :=
    Commons.Analysis.Complex.Dirichlet.dirichlet_ball (c := a) (R := ρ) hρ hF
  have hball : Metric.ball a ρ ⊆ c.target :=
    fun z hz => hsub (Metric.ball_subset_closedBall hz)
  refine ⟨replaceOnDisc c a ρ u (fun x => F (c x)), ?_, ?_, ?_⟩
  · intro x hx
    have hxball : c x ∈ Metric.ball a ρ := hx.2
    have hx' : ‖c x - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hxball
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hu (c x) hx')
    filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with w hw
    exact replaceOnDisc_pullback_of_mem hball hw
  · have hG' : ContinuousOn (fun x => gluedBall u F a ρ (c x)) (chartClosedBall c a ρ) := by
      refine ContinuousOn.congr (f := fun x => (fun z => if ‖z - a‖ < ρ then u z else F z) (c x))
        ?_ ?_
      · exact hG.comp (c.continuousOn.mono (chartClosedBall_subset_source c a ρ))
          (fun x hx => hx.2)
      · intro x hx
        simp only [gluedBall_apply, Metric.mem_ball, dist_eq_norm]
    refine ContinuousOn.congr hG' ?_
    intro x hx
    by_cases hb : x ∈ chartBall c a ρ
    · rw [replaceOnDisc_of_mem_chartBall hb]
      exact (gluedBall_of_mem hb.2).symm
    · have hxs : x ∈ c.source := chartClosedBall_subset_source c a ρ hx
      have hnb : c x ∉ Metric.ball a ρ := fun h => hb ⟨hxs, h⟩
      rw [replaceOnDisc_of_not_mem_chartBall hb]
      exact (gluedBall_of_not_mem hnb).symm
  · intro x hx
    have hxsphere : c x ∈ Metric.sphere a ρ := hx.2
    have hxnot : x ∉ chartBall c a ρ := by
      intro hb
      have h1 : c x ∈ Metric.ball a ρ := hb.2
      rw [Metric.mem_sphere] at hxsphere
      rw [Metric.mem_ball] at h1
      linarith
    rw [replaceOnDisc_of_not_mem_chartBall hxnot]

/-- **Maximum principle on a chart disc.**  If `u` is harmonic on the chart ball, continuous up to
the closed chart disc, and bounded above by `M` on the chart sphere, then `u ≤ M` on the chart
ball. -/
theorem chartBall_le_of_sphere_le {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ M : ℝ}
    (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) {u : X → ℝ}
    (hu : ∀ x ∈ chartBall c a ρ, InnerProductSpace.HarmonicAt (u ∘ c.symm) (c x))
    (hcont : ContinuousOn u (chartClosedBall c a ρ))
    (hbd : ∀ x ∈ chartSphere c a ρ, u x ≤ M) :
    ∀ x ∈ chartBall c a ρ, u x ≤ M := by
  intro x hx
  have hxball : c x ∈ Metric.ball a ρ := hx.2
  have hu' : ∀ w : ℂ, ‖w - a‖ < ρ →
      InnerProductSpace.HarmonicAt (fun w => u (c.symm w)) w := by
    intro w hw
    have hwb : w ∈ Metric.ball a ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwt : w ∈ c.target := hsub (Metric.ball_subset_closedBall hwb)
    have hmem : c.symm w ∈ chartBall c a ρ := by
      refine ⟨c.map_target hwt, ?_⟩
      change c (c.symm w) ∈ Metric.ball a ρ
      rw [c.right_inv hwt]
      exact hwb
    have hthis := hu (c.symm w) hmem
    rw [c.right_inv hwt] at hthis
    exact hthis
  have hFb : ∀ w : ℂ, w ∈ Metric.sphere a ρ → (fun w => u (c.symm w)) w ≤ M := by
    intro w hw
    have hwt : w ∈ c.target := hsub (Metric.sphere_subset_closedBall hw)
    have hmem : c.symm w ∈ chartSphere c a ρ := by
      refine ⟨c.map_target hwt, ?_⟩
      change c (c.symm w) ∈ Metric.sphere a ρ
      rw [c.right_inv hwt]
      exact hw
    exact hbd (c.symm w) hmem
  have hG : ContinuousOn
      (fun w : ℂ => if ‖w - a‖ < ρ then u (c.symm w) else u (c.symm w))
      (Metric.closedBall a ρ) := by
    have heq : (fun w : ℂ => if ‖w - a‖ < ρ then u (c.symm w) else u (c.symm w))
        = fun w => u (c.symm w) := by
      funext w
      by_cases hw : ‖w - a‖ < ρ
      · rw [if_pos hw]
      · rw [if_neg hw]
    rw [heq]
    refine hcont.comp (c.continuousOn_symm.mono hsub) ?_
    intro w hw
    exact ⟨c.map_target (hsub hw), by
      change c (c.symm w) ∈ Metric.closedBall a ρ
      rw [c.right_inv (hsub hw)]
      exact hw⟩
  have h := Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := a) (R := ρ) (M := M)
    hρ hFb hu' hG
  have hx' : u (c.symm (c x)) ≤ M := h (c x) (by simpa [Metric.mem_ball, dist_eq_norm] using hxball)
  rwa [c.left_inv hx.1] at hx'

end Dirichlet

end Submission
