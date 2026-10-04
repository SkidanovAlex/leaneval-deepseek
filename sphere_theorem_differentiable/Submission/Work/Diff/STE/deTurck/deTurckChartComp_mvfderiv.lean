import Mathlib
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.EXT.dOp_koszulPair_eq_sKzD
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.EXT.rmChartExpr_eq_jRm_jet
import Submission.Work.Diff.STE.deTurck.koszulPair_eq_jKz
import Submission.Work.Diff.GE.covRmChartExpr_joint_smooth
import Submission.Work.Diff.GE.joint_deriv
import Submission.Work.Diff.STE.deTurck.ChartCompDefs
import Submission.Work.Diff.STE.deTurck.ChartCompDeriv
import Submission.Work.Diff.STE.deTurck.ChartCompBridge
import Submission.Work.Diff.EXT.chartMat_det_ne_zero
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.deTurck.contMDiffAt_deTurckChartComp_at

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.deTurck

theorem deTurckChartComp_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g gbar : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i c : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q : M => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ q c)
        ((extChartAt I x₀).symm y)
        (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
      = Work.Diff.STE.DeTurck.jdWU (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y)
          (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀)) y)
          (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y)
          (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) gbar x₀)) y) i c := by
  have hps : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have hsrc : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source] at hps
  have hchart : (extChartAt I x₀) ((extChartAt I x₀).symm y) = y := (extChartAt I x₀).right_inv hy
  -- the chart component is smooth at the point, so that the derivative can be read in the chart
  have hmd : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun q : M => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ q c)
      ((extChartAt I x₀).symm y) :=
    (Work.Diff.STE.deTurck.contMDiffAt_deTurckChartComp_at g gbar x₀ hy c).mdifferentiableAt
      (by simp)
  -- chain rule: the manifold derivative is the derivative of the chart representative
  have hchain := Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hsrc
    (g := fun q : M => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ q c) hmd
    (Work.Diff.EXT.bB (E := E) i)
  rw [hchart] at hchain
  -- the chart representative is (eventually) the coordinate expression `coPhi`
  have hev : (fun y' : E => Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀
        ((extChartAt I x₀).symm y') c)
      =ᶠ[nhds y] (fun y' : E => Work.Diff.STE.deTurck.coPhi
        (Work.Diff.EXT.chartMatFun (I := I) g x₀)
        (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) c y') := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hy] with y' hy'
    refine (Work.Diff.STE.deTurck.chartCompB_deTurckChartComp_eq_coPhi g gbar x₀ (by
      have h1 := (extChartAt I x₀).map_target hy'
      rwa [extChartAt_source] at h1) c).trans ?_
    rw [(extChartAt I x₀).right_inv hy']
  rw [show Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y)
      = Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) i) from
    Work.Diff.GE.cFrame_apply x₀ i ((extChartAt I x₀).symm y)]
  rw [hchain, hev.fderiv_eq]
  -- the hypotheses of the coordinate computation
  have hA : ContDiffAt ℝ 2 (Work.Diff.EXT.chartMatFun (I := I) g x₀) y :=
    (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g x₀ hy).of_le (by norm_num)
  have hĀ : ContDiffAt ℝ 2 (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y :=
    (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) gbar x₀ hy).of_le (by norm_num)
  have hdetA : (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)).det ≠ 0 :=
    Work.Diff.EXT.chartMat_det_ne_zero (I := I) g x₀ hy
  have hdetĀ : (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y)).det ≠ 0 :=
    Work.Diff.EXT.chartMat_det_ne_zero (I := I) gbar x₀ hy
  have hsymA : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.chartMatFun (I := I) g x₀ y a b
        = Work.Diff.EXT.chartMatFun (I := I) g x₀ y b a :=
    fun a b => g.symm ((extChartAt I x₀).symm y) _ _
  have hsymĀ : ∀ a b : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y a b
        = Work.Diff.EXT.chartMatFun (I := I) gbar x₀ y b a :=
    fun a b => gbar.symm ((extChartAt I x₀).symm y) _ _
  exact Work.Diff.STE.deTurck.fderiv_coPhi (Work.Diff.EXT.chartMatFun (I := I) g x₀)
    (Work.Diff.EXT.chartMatFun (I := I) gbar x₀) y c i hA hĀ hdetA hdetĀ hsymA hsymĀ

end Work.Diff.STE.deTurck
