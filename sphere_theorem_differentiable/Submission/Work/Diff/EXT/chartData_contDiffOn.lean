import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth
import Submission.Work.Diff.EXT.chartRic_partial_jet
import Submission.CoeffSmooth2
import Submission.Work.Diff.T.lc_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem chartData_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) :
    (∀ t : ℝ, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) K) ∧
    (∀ t : ℝ, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') l i j) K) ∧
    (∀ t : ℝ, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y') i j) K) := by
  -- The chart matrix of each fixed metric is `C^∞` on the whole target of the chart at `x₀`.
  have hbase : ∀ t : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (chartMatFun (I := I) (G t) x₀)
      (extChartAt I x₀).target := fun t y hy =>
    (contDiffAt_chartMatFun (I := I) (G t) x₀ hy).contDiffWithinAt
  refine ⟨?_, ?_, ?_⟩
  · intro t i j
    exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (hbase t) i)) j).mono hKt
  · intro t i j l
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf (G t)) ∞ :=
      Classical.choice (Work.Diff.T.lc_smooth (I := I) (M := M) (G t)).1
    refine (((Submission.Coeff.contDiffOn_chrEntryModel_infty
        (cov := Submission.Diff.lcOf (G t)) x₀ j i).continuousLinearMap_comp
        (((Module.finBasis ℝ E).coord l).toContinuousLinearMap)).mono hKt).congr ?_
    intro y' _
    rfl
  · intro t i j
    exact (((contDiffOn_pi.mp (contDiffOn_pi.mp (hbase t) i)) j).mono hKt).congr
      (fun y' _ => rfl)

end Work.Diff.EXT
