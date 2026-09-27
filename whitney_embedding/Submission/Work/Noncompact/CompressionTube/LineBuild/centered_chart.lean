import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# A chart centred at a point

The piece engine `nc_stage_piece` (and the engines of the proper-ray construction) requires, at each
base point `z`, an open partial homeomorphism `c : M → ℝ^n` with `z ∈ c.source`, `c z = 0` and with
`c.symm` smooth on `c.target`.  Mathlib's `chartAt E z` need *not* be centred (`(chartAt E z) z` is
not `0` in general), so we take `chartAt E z` and compose it with the translation of the model that
moves `(chartAt E z) z` to `0`.  The smoothness of the inverse is transported through
`OpenPartialHomeomorph.coe_trans_symm` from `contMDiffOn_symm_of_mem_maximalAtlas`.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology
open scoped Manifold ContDiff

/-- A chart at `x` centred at `x`: `chartAt E x` followed by the translation of the model by
`-((chartAt E x) x)`. -/
noncomputable def ncChartAt (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  OpenPartialHomeomorph.trans (chartAt (EuclideanSpace ℝ (Fin n)) x)
    (Homeomorph.toOpenPartialHomeomorph
      (Homeomorph.subRight ((chartAt (EuclideanSpace ℝ (Fin n)) x) x)))

theorem ncChartAt_source {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) : x ∈ (ncChartAt n x).source := by
  rw [ncChartAt, OpenPartialHomeomorph.trans_source]
  refine ⟨mem_chart_source _ x, ?_⟩
  rw [Homeomorph.toOpenPartialHomeomorph_source]
  exact mem_univ _

theorem ncChartAt_self {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) : (ncChartAt n x) x = 0 := by
  rw [ncChartAt, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.subRight_apply, sub_self]

theorem contMDiffOn_ncChartAt_symm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    [IsManifold (MC n) smoothOrder M] (x : M) :
    ContMDiffOn (MC n) (MC n) smoothOrder (⇑(ncChartAt n x).symm) (ncChartAt n x).target := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x with hc
  set p : EuclideanSpace ℝ (Fin n) := (chartAt (EuclideanSpace ℝ (Fin n)) x) x with hp
  set τ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    Homeomorph.toOpenPartialHomeomorph (Homeomorph.subRight p) with hτ
  have hc_symm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := MC n) (n := smoothOrder) x)
  have hτ_symm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑τ.symm) τ.target := by
    have hfun : ⇑τ.symm = fun z : EuclideanSpace ℝ (Fin n) => z + p := by
      funext z
      have h1 : (Homeomorph.subRight p) ((Homeomorph.subRight p).symm z) = z :=
        Homeomorph.apply_symm_apply _ z
      rw [Homeomorph.subRight_apply] at h1
      have h2 : (Homeomorph.subRight p).symm z = z + p := by
        rw [sub_eq_iff_eq_add] at h1
        exact h1
      rw [hτ, Homeomorph.toOpenPartialHomeomorph_symm_apply]
      simp only [h2]
    rw [hfun]
    exact (contMDiff_id.add contMDiff_const).contMDiffOn
  have hτ_symm' : ContMDiffOn (MC n) (MC n) smoothOrder (⇑τ.symm)
      (τ.target ∩ ⇑τ.symm ⁻¹' c.target) := hτ_symm.mono Set.inter_subset_left
  have hcomp : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm ∘ ⇑τ.symm)
      (τ.target ∩ ⇑τ.symm ⁻¹' c.target) :=
    hc_symm.comp hτ_symm' Set.inter_subset_right
  have hfun2 : ⇑(ncChartAt n x).symm = ⇑c.symm ∘ ⇑τ.symm := by
    rw [ncChartAt, ← hc, ← hp, ← hτ, OpenPartialHomeomorph.coe_trans_symm]
  have htarget : (ncChartAt n x).target = τ.target ∩ ⇑τ.symm ⁻¹' c.target := by
    rw [ncChartAt, ← hc, ← hp, ← hτ, OpenPartialHomeomorph.trans_target]
  rw [hfun2, htarget]
  exact hcomp

end Work.Noncompact.CompressionTube
