import Mathlib
import Submission.Work.Drive.N2.ChartGlue

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace in
/-- The set of points of the chart target where the `(a,b)`-minor of the chart representation is
invertible is open. -/
theorem isOpen_minorRegion {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin 5)) (he : ContMDiff (𝓡 2) (𝓡 5) ∞ e) (p : M) (a b : Fin 5) :
    IsOpen (Work.Drive.N2.minorRegion e p a b) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyt, hdet⟩
  refine Filter.inter_mem ((chartAt (EuclideanSpace ℝ (Fin 2)) p).open_target.mem_nhds hyt) ?_
  -- the chart representation is `C^∞` at `y`, so its derivative is continuous there
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Projection.chartRep e p) y :=
    Work.Embedding.contDiffAt_chartRepN e he p hyt
  have hcontfd : ContinuousAt (fderiv ℝ (Work.Projection.chartRep e p)) y :=
    ContDiffAt.continuousAt_fderiv hcd (by simp)
  -- hence so is the `(a,b)`-minor, and its determinant
  have hcomp : ContinuousAt
      (fun z => (depProj a b).comp (fderiv ℝ (Work.Projection.chartRep e p) z)) y :=
    continuousAt_const.clm_comp hcontfd
  have hdetcont : ContinuousAt
      (fun z => (minor (Work.Projection.chartRep e p) a b z).det) y :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hcomp
  exact hdetcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hdet)

end Work.Drive.N2
