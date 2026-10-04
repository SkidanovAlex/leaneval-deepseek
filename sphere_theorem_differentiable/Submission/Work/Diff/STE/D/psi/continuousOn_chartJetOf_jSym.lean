import Mathlib
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.D.ChartData_jVec
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the chart `2`-jet of the symmetrised Galerkin family

`Work.Diff.STE.D.chartJetOf h x₀ y` is the spatial `2`-jet (value, first and second Fréchet
derivative in the chart coordinate `y`) of the chart matrix of a section `h`.  The target theorem
says that for every member `jSym D ε z` of the symmetrised spanning family of the Galerkin scheme,
this `2`-jet is continuous on the chart target of `x₀`.

The proof is an immediate assembly of two ingredients that are already available:

* every `jSym D ε z` has smooth chart data (`Work.Diff.STE.D.psi.jSym_chartData`, from
  `ChartData_genMap` and `ChartData_jVec`), i.e. its chart matrix is `C^∞` in the chart
  coordinate;
* the spatial `2`-jet of the chart matrix of a section with smooth chart data is `C^∞` on the
  chart target (`Work.Diff.STE.D.psi.contDiffOn_chartJetOf`); in particular it is continuous.
-/

namespace Work.Diff.STE.D.psi

theorem continuousOn_chartJetOf_jSym
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ContinuousOn (fun y : E => Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (jSym (I := I) (M := M) D ε z) x₀ y) (extChartAt I x₀).target := by
  exact (contDiffOn_chartJetOf (I := I) (M := M) (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
    x₀ (jSym_chartData (I := I) (M := M) D ε z x₀)).continuousOn

end Work.Diff.STE.D.psi
