import Mathlib
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.ricJetDefs
import Submission.Work.Diff.EXT.koszulPair_eq_sKz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.deTurck

theorem koszulPair_eq_jKz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source)
    (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (fun _ : ℝ => g) (I := I) x₀ a b c 0 p
      = Work.Diff.EXT.jKz (fderiv ℝ (Work.Diff.EXT.chartMatFun g x₀)
            ((extChartAt I x₀) p)) a b c := by
  have hpsrc : p ∈ (extChartAt I x₀).source := by
    rwa [extChartAt_source]
  have hy : (extChartAt I x₀) p ∈ (extChartAt I x₀).target :=
    PartialEquiv.map_source _ hpsrc
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p :=
    PartialEquiv.left_inv _ hpsrc
  have h := Work.Diff.EXT.koszulPair_eq_sKz (I := I) (M := M) g x₀ hy a b c
  rw [hsymm] at h
  rw [h]
  rfl

end Work.Diff.STE.deTurck
