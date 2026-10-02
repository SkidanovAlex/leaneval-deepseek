import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the properties of the region charted

The inclusion of the region `{Φ ≤ 0}` into `A` is `C^∞`, hence so is the post-composition of any
`C^∞` map on `A`; the chart target is a neighbourhood of the base point within the model; and the
pullback charts of ambient charts of the maximal atlas are charts of the maximal atlas of the region.
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

/-- **The value of the extended region chart at a point of the half-space.** -/
theorem extend_symm_val (m : S.Region) {y : Mod k} (hy : y ∈ Set.range (𝓡∂ (8 + k + 1)))
    (hct : (𝓡∂ (8 + k + 1)).symm y ∈ S.chartTarget m) :
    ((S.domExt m) ∘ Subtype.val
        ∘ ((S.chartAt m).extend (𝓡∂ (8 + k + 1))).symm) y
      = (S.T m).symm y := by
  have hct' : (S.T m).symm ((𝓡∂ (8 + k + 1)).symm y).1 ∈ (S.domExt m).target
      ∧ ((𝓡∂ (8 + k + 1)).symm y).1 ∈ (S.T m).target := by
    have h0 : (𝓡∂ (8 + k + 1)).symm y ∈ S.chartTarget m := hct
    simpa only [chartTarget, chartImageSet, Set.mem_ofPred_eq] using h0
  have h1 : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))).symm y
      = (⟨S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y),
          S.chartInvVal_mem_region m hct⟩ : S.Region) := by
    rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
    rw [chartAt_symm_apply]
    exact dif_pos hct
  have h2 : S.domExt m (S.chartInvVal m ((𝓡∂ (8 + k + 1)).symm y)) = (S.T m).symm y := by
    rw [chartInvVal, PartialEquiv.right_inv _ hct'.1, symm_val_of_mem_range hy]
  rw [Function.comp_apply, Function.comp_apply, h1, h2]

/-- The preimage of the target of the chart at `m` is a neighbourhood of the base point within the
half-space. -/
theorem chartTarget_mem_nhdsWithin (m : S.Region) :
    (𝓡∂ (8 + k + 1)).symm ⁻¹' S.chartTarget m ∈
      𝓝[Set.range (𝓡∂ (8 + k + 1))] (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m) := by
  obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp (S.isOpen_chartTarget m)
  have hmemW : ((S.chartAt m) m) ∈ Subtype.val ⁻¹' W := by
    rw [hW]
    exact (S.chartAt m).map_source (mem_chart_source (Half k) m)
  have hxW : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m ∈ W := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_apply]
    exact hmemW
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨W, hWopen.mem_nhds hxW, ?_⟩
  rintro y ⟨hyW, hyI⟩
  rw [Set.mem_preimage, ← hW, Set.mem_preimage,
    show (((𝓡∂ (8 + k + 1)).symm y : Half k)).1 = y from symm_val_of_mem_range hyI]
  exact hyW

/-- **The inclusion of the region in the ambient manifold is smooth.** -/
theorem contMDiff_val :
    ContMDiff (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞ (fun m : S.Region => m.1) := by
  intro m
  have hxI : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m ∈ Set.range (𝓡∂ (8 + k + 1)) :=
    ⟨(S.chartAt m) m, rfl⟩
  have h2 : (𝓡∂ (8 + k + 1)).symm (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m)
      = (S.chartAt m) m := by
    show (𝓡∂ (8 + k + 1)).symm ((𝓡∂ (8 + k + 1)) ((S.chartAt m) m)) = (S.chartAt m) m
    exact ModelWithCorners.left_inv (𝓡∂ (8 + k + 1)) ((S.chartAt m) m)
  have hxct : (𝓡∂ (8 + k + 1)).symm (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m)
      ∈ S.chartTarget m := by
    rw [h2]
    exact (S.chartAt m).map_source (mem_chart_source (Half k) m)
  rw [contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ (8 + k + 1)) m) (S.dom_maximalAtlas m)
    (mem_chart_source (Half k) m) (S.mem_dom_source m)]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hchart : ((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m = S.chartVec m m.1 := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      S.chartAt_apply_of_mem m (S.mem_chartSource_self m),
      modelWithCornersEuclideanHalfSpace_apply]
  have hz1 : (S.T m) (S.domExt m m.1) ∈ (S.T m).target :=
    (S.T m).map_source (S.mem_T_source m)
  have hsm : ContDiffWithinAt ℝ ∞ ((S.T m).symm : Mod k → Mod k)
      (Set.range (𝓡∂ (8 + k + 1))) (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m) := by
    rw [hchart]
    exact ((S.T_symm_smooth m).contDiffAt
      ((S.T m).open_target.mem_nhds hz1)).contDiffWithinAt
  have hev : (((S.domExt m) : S.A → Mod k) ∘ Subtype.val
        ∘ ((S.chartAt m).extend (𝓡∂ (8 + k + 1))).symm)
      =ᶠ[𝓝[Set.range (𝓡∂ (8 + k + 1))] (((S.chartAt m).extend (𝓡∂ (8 + k + 1))) m)]
      ((S.T m).symm : Mod k → Mod k) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.range (𝓡∂ (8 + k + 1)) ∩ ((𝓡∂ (8 + k + 1)).symm ⁻¹' S.chartTarget m), ?_, ?_⟩
    · exact Filter.inter_mem self_mem_nhdsWithin (S.chartTarget_mem_nhdsWithin m)
    · intro y hy
      exact S.extend_symm_val m hy.1 hy.2
  refine hsm.congr_of_eventuallyEq ?_ ?_
  · exact hev
  · exact S.extend_symm_val m hxI hxct

/-- The inclusion of the region in the ambient manifold is smooth, on any set. -/
theorem contMDiffOn_val (W : Set S.A) :
    ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓡∂ (8 + k + 1)) ∞ (fun m : S.Region => m.1)
      {m : S.Region | m.1 ∈ W} :=
  S.contMDiff_val.contMDiffOn

/-- **Post-composition with the inclusion of the region.** -/
theorem contMDiffOn_comp_val (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : S.A → F) (W : Set S.A)
    (hf : ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ f W) :
    ContMDiffOn (𝓡∂ (8 + k + 1)) (𝓘(ℝ, F)) ∞ (fun m : S.Region => f m.1)
      {m : S.Region | m.1 ∈ W} :=
  hf.comp (S.contMDiffOn_val W) (fun _ hm => hm)

end RegionSetupWeak

end

end Work.PTGeometric.WeakRegion
