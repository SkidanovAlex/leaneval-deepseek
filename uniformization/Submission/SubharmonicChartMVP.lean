import ChallengeDeps
import Submission.RiemannSurface
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue

/-!
# The circle mean-value inequality in an arbitrary chart

`Submission.SubharmonicOnX u U` (Hubbard's Definition 1.2.1, in the formulation of
`Submission/RiemannSurface.lean`) requires, at each point `y ∈ U`, the circle mean-value inequality
*in the preferred chart at `y`*, and only for circles inside a ball whose radius is chosen together
with the point.  For the comparison arguments of the Green-function construction one needs the
inequality in a *fixed* chart `c` and for *all* circles inside a fixed ball `B ⊆ c.target` with
`c.symm '' B ⊆ U`.

The passage from the pointwise-local formulation to this global one is the classical fact that a
locally subharmonic function satisfies the mean-value inequality on every circle contained in its
domain.  Here it is obtained from the commons lemma
`Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue` (which is exactly that
fact, stated for continuous functions on an open subset of `ℂ`), applied to the pullback
`u ∘ c.symm` on the chart ball; the *pointwise* local inequality for the pullback is supplied by the
chart-independence of subharmonicity `Submission.SubharmonicAtChart_iff_chartAt`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The circle mean-value inequality of a subharmonic function in an arbitrary chart.** -/
theorem SubharmonicOnX.chart_mvp {U : Set X} (hU : IsOpen U) {u : X → ℝ}
    (hu : SubharmonicOnX u U) {z : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hρsub : Metric.ball ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target)
    (hρU : (chartAt ℂ z).symm '' Metric.ball ((chartAt ℂ z) z) ρ ⊆ U) :
    ∀ p ∈ Metric.ball ((chartAt ℂ z) z) ρ, ∀ r : ℝ, 0 < r →
      Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ z) z) ρ →
      (u ∘ (chartAt ℂ z).symm) p ≤ Real.circleAverage (u ∘ (chartAt ℂ z).symm) p r := by
  have hcont : ContinuousOn (u ∘ (chartAt ℂ z).symm) (Metric.ball ((chartAt ℂ z) z) ρ) :=
    hu.1.comp (((chartAt ℂ z).continuousOn_symm).mono (fun w hw => hρsub hw))
      (fun w hw => hρU ⟨w, hw, rfl⟩)
  refine Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_localSubMeanValue
    Metric.isOpen_ball hcont ?_
  intro p hp
  have hpsrc : (chartAt ℂ z).symm p ∈ (chartAt ℂ z).source :=
    (chartAt ℂ z).map_target (hρsub hp)
  have hpU : (chartAt ℂ z).symm p ∈ U := hρU ⟨p, hp, rfl⟩
  have hchart : SubharmonicAtChart u (chartAt ℂ z) ((chartAt ℂ z).symm p) :=
    (SubharmonicAtChart_iff_chartAt (u := u) (a := (chartAt ℂ z).symm p) (b := z)
      hpsrc).mp (hu.2 _ hpU)
  obtain ⟨-, ρ', hρ', htgt', hcont', hmvp'⟩ := hchart
  have hpeq : (chartAt ℂ z) ((chartAt ℂ z).symm p) = p := (chartAt ℂ z).right_inv (hρsub hp)
  rw [hpeq] at hmvp'
  refine ⟨min ρ' (ρ - dist p ((chartAt ℂ z) z)), lt_min hρ' (by
    have := Metric.mem_ball.mp hp; linarith), ?_, ?_⟩
  · intro q hq
    rw [Metric.mem_ball] at hq ⊢
    calc dist q ((chartAt ℂ z) z) ≤ dist q p + dist p ((chartAt ℂ z) z) := dist_triangle _ _ _
      _ < min ρ' (ρ - dist p ((chartAt ℂ z) z)) + dist p ((chartAt ℂ z) z) := by linarith
      _ ≤ (ρ - dist p ((chartAt ℂ z) z)) + dist p ((chartAt ℂ z) z) := by
            linarith [min_le_right ρ' (ρ - dist p ((chartAt ℂ z) z))]
      _ = ρ := by ring
  · intro r hr hrsub
    have hsub' : Metric.closedBall p r ⊆ Metric.ball p ρ' :=
      hrsub.trans (Metric.ball_subset_ball (min_le_left _ _))
    exact hmvp' p (Metric.mem_ball_self hρ') r hr hsub'

end Submission
