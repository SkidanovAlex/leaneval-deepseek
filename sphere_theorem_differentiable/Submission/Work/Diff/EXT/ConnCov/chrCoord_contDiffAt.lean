import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.aComp_eq_koszulPair_sub
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart Christoffel symbols in the chart coordinate

The chart Christoffel symbols `Work.Diff.GE.chrCoord G x₀ n a b t y` of the metric `G t` are the
inverse-Gram contraction `∑ p, γ^{np} Γ_{abp}` of the Koszul pairings
`koszulPair G x₀ a b p t y = ⟨∇_{σ_a}σ_b, σ_p⟩` (`Work.Diff.GE.chrCoord`).

They agree — with the *second and third* index interchanged — with the chart Christoffel symbol
`Work.Diff.GE.cGam (G t) x₀ y n b a` of the chart library, which is known to be smooth in the
chart coordinate: `Work.Diff.EXT.ConnCov.cGam_eq_mulVec_koszulPair` identifies
`cGam (G t) x₀ y n b a` with `(GramInv) *ᵥ (fun m ↦ koszulPair G x₀ a b m t y) n`, and
`Work.Diff.EXT.CBound.cGam_contDiffAt_of_target` gives the `ContDiffAt`.  This is the only
structural smoothness input of the chart recursions for the moving tower of the curvature
(`Work.Diff.EXT.ConnCov.rmChartTower`).
-/

namespace Work.Diff.EXT.ConnCov

theorem chrCoord_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (p a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.chrCoord (I := I) G x₀ p a b t
        (Work.Diff.EXT.pt (I := I) x₀ y')) y := by
  -- The chart Christoffel symbol `cGam (G t) x₀ · n b a` of the chart library is smooth.
  have hbase :=
    Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G t) x₀ hy p b a
  -- It agrees with `chrCoord G x₀ p a b t ·` (with the last two indices swapped) on the chart.
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hy] with y' hy'
  rw [Work.Diff.EXT.ConnCov.cGam_eq_mulVec_koszulPair (I := I) (M := M) G x₀ t hy' p b a]
  simp only [Work.Diff.GE.chrCoord, Matrix.mulVec_apply_eq_sum]

end Work.Diff.EXT.ConnCov
