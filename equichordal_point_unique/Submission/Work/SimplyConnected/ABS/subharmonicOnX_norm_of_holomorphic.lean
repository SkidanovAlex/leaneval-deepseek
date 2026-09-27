import Mathlib
import Submission.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Holomorphic
import Submission.SubharmonicChartMVP

/-!
# The modulus of a holomorphic function is subharmonic

A general, reusable library fact for the uniformization project: on a complex one-manifold `X`,

`z ↦ ‖R z‖` is subharmonic on every open set `U` on which `R : X → ℂ` is holomorphic.

In the disk model this is the classical statement that `|f|` is subharmonic for `f` holomorphic
(for `p ≥ 1`, `|f|^p` is subharmonic; `p = 1` is the case needed by the Green-function argument of
`norm_le_exp_neg_of_modulus`, where the bound `‖R‖ ≤ 1` is deduced from the boundary values of `‖R‖`
on the frontier of `{E > ε}`).

## Proof

`Submission.SubharmonicOnX u U` (Hubbard's Definition 1.2.1) asks, at each `x ∈ U`, for the chart
condition `Submission.SubharmonicAtChart u (chartAt ℂ x) x`: a radius `ρ > 0` with
`ball (c x) ρ ⊆ c.target`, continuity of `u ∘ c.symm` on the ball, and the circle mean-value
inequality `(u ∘ c.symm) p ≤ circleAverage (u ∘ c.symm) p r` for all circles inside the ball.

For `u := fun z => ‖R z‖` and `c := chartAt ℂ x`, the pullback `G := R ∘ c.symm` is analytic (hence
continuous and differentiable) on a ball around `c x` inside `c.target`; the analytic input is

* the **mean value property** `circleAverage G p r = G p` for `G` differentiable on `ball p r`:
  `DiffContOnCl.circleAverage (hf : DiffContOnCl ℂ G (ball p r))`
  (`Mathlib/Analysis/Complex/MeanValue.lean:111`), where `DiffContOnCl ℂ G (ball p r)` is obtained
  from analyticity of `G` on a ball containing `closedBall p r` (differentiability inside plus
  continuity on the closed ball); together with
* the **norm-of-average bound** `‖circleAverage G p r‖ ≤ circleAverage (fun w => ‖G w‖) p r`.
  For `ℝ`-valued `G` this is `abs_circleAverage_le_circleAverage_abs`
  (`Mathlib/MeasureTheory/Integral/CircleAverage.lean:293`); for `ℂ`-valued `G` reduce to the real
  case with `ContinuousLinearMap.circleAverage_comp_comm` (line 317) applied to `Complex.reCLM`
  composed with the unit scalars, or prove the general norm bound by
  `norm_integral_le_integral_norm` after unfolding `Real.circleAverage_def`.

**Qualified name.**  The general definition `circleAverage : E` (for a normed space `E`) sits
*inside* `namespace Real` in `Mathlib/MeasureTheory/Integral/CircleAverage.lean`, so its qualified
name is `Real.circleAverage` — this is the name to use for both `ℝ`- and `ℂ`-valued integrands
(the unqualified `circleAverage` is not in scope).

These give `‖G p‖ = ‖circleAverage G p r‖ ≤ circleAverage (fun w => ‖G w‖) p r`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The modulus of a holomorphic function is subharmonic.**  For `R` holomorphic on the open set
`U`, the function `z ↦ ‖R z‖` satisfies Hubbard's circle mean-value inequality on `U`. -/
theorem subharmonicOnX_norm_of_holomorphic {U : Set X} {R : X → ℂ}
    (hR : Submission.HolomorphicOnX R U) :
    Submission.SubharmonicOnX (fun z : X => ‖R z‖) U := by
  refine ⟨continuousOn_of_forall_continuousAt fun x hx => ((hR x hx).continuousAt).norm,
    fun x hx => ?_⟩
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  have hxsrc : x ∈ c.source := mem_chart_source ℂ x
  have han : AnalyticAt ℂ (R ∘ c.symm) (c x) := hR x hx
  obtain ⟨ρ, hρ, hρana⟩ := han.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, Metric.ball (c x) ε ⊆ c.target := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp c.open_target (c x) (c.map_source hxsrc)
    exact ⟨ε, hε, hεsub⟩
  refine ⟨hxsrc, min ρ ε, lt_min hρ hε,
    (Metric.ball_subset_ball (min_le_right _ _)).trans hεsub,
    ((hρana.mono (Metric.ball_subset_ball (min_le_left _ _))).continuousOn).norm, ?_⟩
  intro p hp r hr hsub
  have hinner : Metric.closedBall p r ⊆ Metric.ball (c x) ρ :=
    hsub.trans (Metric.ball_subset_ball (min_le_left _ _))
  have han' : AnalyticOnNhd ℂ (R ∘ c.symm) (Metric.ball (c x) (min ρ ε)) :=
    hρana.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hD : DiffContOnCl ℂ (R ∘ c.symm) (Metric.ball p r) :=
    DiffContOnCl.mk_ball
      ((han'.mono (Metric.ball_subset_closedBall.trans hsub)).differentiableOn)
      ((han'.continuousOn).mono hsub)
  have hDmvp : DiffContOnCl ℂ (R ∘ c.symm) (Metric.ball p |r|) := by
    rw [abs_of_pos hr]
    exact hD
  have hmvp : Real.circleAverage (R ∘ c.symm) p r = (R ∘ c.symm) p :=
    DiffContOnCl.circleAverage hDmvp
  calc ‖(R ∘ c.symm) p‖ = ‖Real.circleAverage (R ∘ c.symm) p r‖ := by rw [hmvp]
    _ ≤ Real.circleAverage (fun w => ‖(R ∘ c.symm) w‖) p r := by
        rw [Real.circleAverage_def, Real.circleAverage_def, norm_smul,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹), smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_integral_norm (by positivity)) (by positivity)

end Work.SimplyConnected.ABS
