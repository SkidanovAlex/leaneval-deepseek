import Mathlib
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_jets
import Submission.Work.Diff.GE.rmChartExpr_joint_smooth
import Submission.Work.Diff.EXT.chartRic_partial_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology

namespace Work.Diff.EXT.ConnCov

theorem rmChartExpr_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t
        (Work.Diff.EXT.pt (I := I) x₀ y')) y := by
  -- The metric `G t` is a single smooth metric; equip the tangent bundle with its Riemannian
  -- structure so that the chart-smoothness machinery is available.
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  -- The constant family `fun _ => G t` is jointly smooth.
  have hJs : Submission.Diff.JointSmooth (fun _ : ℝ => G t) (Set.Ico 0 1) := by
    have h0 : Submission.Diff.JointSmooth (fun _ : ℝ => G t) (Set.univ : Set ℝ) :=
      Work.Diff.EXT.jointSmooth_const (I := I) (M := M) (G t)
    exact h0.mono (fun p _ => ⟨Set.mem_univ p.1, Set.mem_univ p.2⟩)
  -- Joint smoothness of the chart curvature array.
  have hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => G t) x₀ i j k l p.1 p.2)
      (Set.Ico 0 1 ×ˢ (chartAt H x₀).source) :=
    Work.Diff.GE.rmChartExpr_joint_smooth (I := I) (G := fun _ : ℝ => G t) hJs x₀
      (fun hu hX => Work.Diff.GE.joint_deriv hu hX) i j k l
  -- The point of the chart at `x₀` with coordinate `y`.
  have hx : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  -- Restrict to the time slice, and pull back to the model space.
  have hman : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => G t) x₀ i j k l 0 y')
      (Work.Diff.EXT.pt (I := I) x₀ y) :=
    (Work.Diff.GE.slice_contMDiffWithinAt (I := I) (M := M)
      (u := fun s y' => Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => G t) x₀ i j k l s y')
      (T := 1) (t := 0) (U := (chartAt H x₀).source)
      ⟨le_rfl, by norm_num⟩ hjoint hx).contMDiffAt
      ((chartAt H x₀).open_source.mem_nhds hx)
  have hsymm : ContMDiffAt (𝓘(ℝ, E)) I ∞ (fun z : E => (extChartAt I x₀).symm z) y :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => G t) x₀ i j k l 0
        (Work.Diff.EXT.pt (I := I) x₀ y')) y :=
    contMDiffAt_iff_contDiffAt.mp (hman.comp y hsymm)
  -- For the constant family, the time parameter is irrelevant.
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
  rfl

end Work.Diff.EXT.ConnCov
