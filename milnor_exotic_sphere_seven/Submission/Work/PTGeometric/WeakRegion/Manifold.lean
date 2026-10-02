import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Region

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the weak region-charting theorem — the smooth structure

The charts `chartAt m` of the region are compatible, so they define a `ChartedSpace` and a `C^∞`
manifold with boundary; the region is compact and `T2`, and its boundary is
`(∂A ∩ region) ∪ {Φ = 0}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric.WeakRegion

noncomputable section

namespace RegionSetupWeak

variable {k : ℕ} (S : RegionSetupWeak k)

theorem symm_val_of_mem_range {y : Mod k} (hy : y ∈ Set.range (𝓡∂ (8 + k + 1))) :
    ((𝓡∂ (8 + k + 1)).symm y).1 = y := by
  obtain ⟨u, rfl⟩ := hy
  exact congrArg Subtype.val ((𝓡∂ (8 + k + 1)).left_inv u)

theorem chartAt_symm_apply (m : S.Region) (u : Half k) :
    (S.chartAt m).symm u = if hu : u ∈ S.chartTarget m then
      (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region) else m := rfl

theorem transAux_eq_chartAt_trans (m m' : S.Region) {y : Mod k}
    (hy : y ∈ Set.range (𝓡∂ (8 + k + 1))) (hct : (𝓡∂ (8 + k + 1)).symm y ∈ (S.chartAt m).target)
    (hcs : (S.chartAt m).symm ((𝓡∂ (8 + k + 1)).symm y) ∈ (S.chartAt m').source) :
    S.transAux m m' y = (𝓡∂ (8 + k + 1))
      (((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)) := by
  have hyv : ((𝓡∂ (8 + k + 1)).symm y).1 = y := symm_val_of_mem_range hy
  have hsymm : (S.chartAt m).symm ((𝓡∂ (8 + k + 1)).symm y)
      = (⟨S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y),
          S.chartInvVal_mem_region m hct⟩ : S.Region) := by
    rw [chartAt_symm_apply]
    exact dif_pos hct
  have hcs' : (⟨S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y),
      S.chartInvVal_mem_region m hct⟩ : S.Region) ∈ S.chartSource m' := by
    rw [← hsymm]; exact hcs
  have htrans : ((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)
      = (⟨S.chartVec m' (S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y)),
          S.chartVec_nonneg m' hcs'⟩ : Half k) := by
    rw [OpenPartialHomeomorph.trans_apply, hsymm]
    exact S.chartAt_apply_of_mem m' hcs'
  rw [htrans]
  show S.transAux m m' y = S.chartVec m' (S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y))
  rw [transAux, chartVec, chartInvVal, hyv]

theorem contDiffOn_chartAt_trans (m m' : S.Region) :
    ContDiffOn ℝ ∞ (fun y : Mod k => (𝓡∂ (8 + k + 1))
      (((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)))
      ((𝓡∂ (8 + k + 1)).symm ⁻¹' ((S.chartAt m).symm ≫ₕ (S.chartAt m')).source
        ∩ Set.range (𝓡∂ (8 + k + 1))) := by
  set Sset : Set (Mod k) := (𝓡∂ (8 + k + 1)).symm ⁻¹'
      ((S.chartAt m).symm ≫ₕ (S.chartAt m')).source ∩ Set.range (𝓡∂ (8 + k + 1)) with hSset
  have hct_of : ∀ y ∈ Sset, (𝓡∂ (8 + k + 1)).symm y ∈ (S.chartAt m).target := by
    intro y hy
    have h := hy.1
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h.1
  have hcs_of : ∀ y ∈ Sset,
      (S.chartAt m).symm ((𝓡∂ (8 + k + 1)).symm y) ∈ (S.chartAt m').source := by
    intro y hy
    have h := hy.1
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
    exact h.2
  have hsub : Sset ⊆ S.transSource m m' := by
    intro y hy
    have hct := hct_of y hy
    have hcs := hcs_of y hy
    have h0 : (𝓡∂ (8 + k + 1)).symm y ∈ S.chartTarget m := hct
    have hct' : (S.T m).symm ((𝓡∂ (8 + k + 1)).symm y).1 ∈ (S.domExt m).target
        ∧ ((𝓡∂ (8 + k + 1)).symm y).1 ∈ (S.T m).target := by
      simpa only [chartTarget, chartImageSet, Set.mem_ofPred_eq] using h0
    have hyv : ((𝓡∂ (8 + k + 1)).symm y).1 = y := symm_val_of_mem_range hy.2
    have hsymm : (S.chartAt m).symm ((𝓡∂ (8 + k + 1)).symm y)
        = (⟨S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y),
            S.chartInvVal_mem_region m hct⟩ : S.Region) := by
      rw [chartAt_symm_apply]
      exact dif_pos hct
    have hcs'' : (⟨S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y),
        S.chartInvVal_mem_region m hct⟩ : S.Region) ∈ S.chartSource m' := by
      rw [← hsymm]; exact hcs
    have hzT : (S.T m).symm y ∈ (S.domExt m).target := by
      rw [← hyv]; exact hct'.1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hyv]; exact hct'.2
    · rw [← OpenPartialHomeomorph.extend_image_source_inter (S.dom m) (S.dom m')]
      refine ⟨S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y),
        ⟨S.chartInvVal_mem_source m hct, hcs''.1⟩, ?_⟩
      calc S.domExt m (S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y))
          = S.domExt m ((S.domExt m).symm ((S.T m).symm y)) := by rw [chartInvVal, hyv]
        _ = (S.T m).symm y := PartialEquiv.right_inv _ hzT
    · rw [← hyv]; exact hcs''.2
  have heq : ∀ y ∈ Sset, S.transAux m m' y = (𝓡∂ (8 + k + 1))
      (((S.chartAt m).symm ≫ₕ (S.chartAt m')) ((𝓡∂ (8 + k + 1)).symm y)) :=
    fun y hy => S.transAux_eq_chartAt_trans m m' hy.2 (hct_of y hy) (hcs_of y hy)
  refine ((S.contDiffOn_transAux m m').mono hsub).congr ?_
  intro y hy
  exact (heq y hy).symm

/-- The charted space structure on the region. -/
noncomputable def chartedSpaceOfRegion : ChartedSpace (Half k) S.Region where
  atlas := Set.range (S.chartAt)
  chartAt := S.chartAt
  mem_chart_source m := S.mem_chartSource_self m
  chart_mem_atlas m := ⟨m, rfl⟩

attribute [instance] chartedSpaceOfRegion

/-- The smooth structure on the region. -/
theorem isManifoldOfRegion : IsManifold (𝓡∂ (8 + k + 1)) ∞ S.Region := by
  refine isManifold_of_contDiffOn (𝓡∂ (8 + k + 1)) ∞ S.Region (fun e e' he he' => ?_)
  obtain ⟨m, rfl⟩ := he
  obtain ⟨m', rfl⟩ := he'
  exact S.contDiffOn_chartAt_trans m m'

/-- The region is compact. -/
theorem compactSpaceOfRegion : CompactSpace S.Region :=
  isCompact_iff_compactSpace.mp S.hK

/-- The region is a `T2` space. -/
theorem t2SpaceOfRegion : T2Space S.Region := inferInstance

attribute [instance] isManifoldOfRegion compactSpaceOfRegion t2SpaceOfRegion

/-- **The boundary of the region** is `(∂A ∩ region) ∪ {Φ = 0}`. -/
theorem mem_boundary_iff (m : S.Region) :
    m ∈ (𝓡∂ (8 + k + 1)).boundary S.Region ↔
      (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0) := by
  have he : S.chartAt m ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.Region :=
    IsManifold.chart_mem_maximalAtlas m
  rw [Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
    (m := 8 + k + 1) he (mem_chart_source (Half k) m)]
  have hval : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m = S.chartVec m m.1 := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      S.chartAt_apply_of_mem m (S.mem_chartSource_self m),
      modelWithCornersEuclideanHalfSpace_apply]
  rw [hval]
  exact S.base_coord_zero m

end RegionSetupWeak

end

end Work.PTGeometric.WeakRegion
