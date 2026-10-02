import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Atlas
import Submission.Work.ThomBordism.Grassmann.Smooth.chartModelEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The oriented Grassmannian as a smooth manifold modelled on `ℝ^{km}`

The charts of `Work.ThomBordism.Grassmann.Smooth.Chart.Atlas` take values in the space of
continuous linear maps `Amb k →L[ℝ] Amb m`, which is linearly isometric to `ℝ^{k*m}`.  This module
re-charts the atlas over the Euclidean model, exactly as `Work.Projective.Model` does for `ℂPⁿ`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Manifold ContDiff Topology
open Set

noncomputable section

variable {k m : ℕ}

/-- A chosen linear isometry from the model space of the graph charts to `ℝ^{k*m}`. -/
def linEquiv (k m : ℕ) : (Amb k →L[ℝ] Amb m) ≃L[ℝ] EuclideanSpace ℝ (Fin (k * m)) :=
  Classical.choice (chartModelEquiv k m)

/-- The chart of the oriented Grassmannian over the Euclidean model. -/
def euclidChart (S : ChartIdx k m) (ε : ℝ) :
    OpenPartialHomeomorph (OG k m) (EuclideanSpace ℝ (Fin (k * m))) :=
  (chart S ε).trans ((linEquiv k m).toHomeomorph.toOpenPartialHomeomorph :
    OpenPartialHomeomorph (Amb k →L[ℝ] Amb m) (EuclideanSpace ℝ (Fin (k * m))))

/-- The atlas of the oriented Grassmannian over the Euclidean model. -/
def euclidAtlas (k m : ℕ) :
    Set (OpenPartialHomeomorph (OG k m) (EuclideanSpace ℝ (Fin (k * m)))) :=
  Set.range (fun i : AtlasIdx k m => euclidChart i.1 i.2)

theorem euclidChart_mem_atlas (S : ChartIdx k m) (ε : ℝ) :
    euclidChart S ε ∈ euclidAtlas k m := ⟨(S, ε), rfl⟩

instance instChartedSpaceEuclid (k m : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (k * m))) (OG k m) where
  atlas := euclidAtlas k m
  chartAt x := euclidChart (Classical.choose (exists_mem_chartSrc x)).1
    (Classical.choose (exists_mem_chartSrc x)).2
  mem_chart_source x := by
    have h := Classical.choose_spec (exists_mem_chartSrc x)
    rw [euclidChart, OpenPartialHomeomorph.trans_source]
    exact ⟨h, Set.mem_univ _⟩
  chart_mem_atlas x := euclidChart_mem_atlas _ _

theorem euclid_symm_trans_mem (S T : ChartIdx k m) (ε ε' : ℝ) :
    (euclidChart S ε).symm ≫ₕ (euclidChart T ε') ∈
      contDiffGroupoid ∞ (𝓘(ℝ, EuclideanSpace ℝ (Fin (k * m)))) := by
  have h := Work.Model.conj_mem (linEquiv k m).toHomeomorph (linEquiv k m).contDiff
    (linEquiv k m).symm.contDiff (chart_symm_trans_chart_mem S T ε ε')
  convert h using 2
  rw [euclidChart, euclidChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  simp only [OpenPartialHomeomorph.trans_assoc]

/-- **The oriented Grassmannian is a smooth manifold modelled on `ℝ^{k*m}`.** -/
instance instIsManifoldEuclid (k m : ℕ) :
    IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin (k * m)))) ∞ (OG k m) where
  compatible := by
    intro e e' he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact euclid_symm_trans_mem i.1 j.1 i.2 j.2

end

end Work.ThomBordism.Grassmann.Smooth
