import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Setup
import Submission.Work.ThomBordism.exists_chartData_pinned

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the weak region-charting theorem — the charted space

From the per-point chart data `Work.PTGeometric.WeakRegion.RegionSetupWeak.exists_chartData` we build
the charts of the region `{Φ ≤ 0}`, prove that they form a `ChartedSpace` and a `C^∞` manifold with
boundary, that the region is compact and `T2`, that the boundary of the region is
`(∂A ∩ region) ∪ {Φ = 0}`, and that the inclusion of the region into `A` is `C^∞`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
-- set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric.WeakRegion

noncomputable section

namespace RegionSetupWeak

variable {k : ℕ} (S : RegionSetupWeak k)

/-! ## The chart data -/

/-- The chart data at `m`: an ambient chart `dom m` and a model chart `T m`. -/
noncomputable def chartData (m : S.Region) :
    OpenPartialHomeomorph S.A (Half k) × OpenPartialHomeomorph (Mod k) (Mod k) :=
  ⟨Classical.choose (Work.ThomBordism.exists_chartData_pinned k S m),
    Classical.choose (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))⟩

/-- The ambient chart at `m`. -/
noncomputable def dom (m : S.Region) : OpenPartialHomeomorph S.A (Half k) :=
  (S.chartData m).1

/-- The model chart at `m`. -/
noncomputable def T (m : S.Region) : OpenPartialHomeomorph (Mod k) (Mod k) :=
  (S.chartData m).2

theorem dom_maximalAtlas (m : S.Region) :
    S.dom m ∈ IsManifold.maximalAtlas (𝓡∂ (8 + k + 1)) ∞ S.A :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).1

theorem mem_dom_source (m : S.Region) : m.1 ∈ (S.dom m).source :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.1

/-- The extended ambient chart at `m` (from `A` into the model space). -/
abbrev domExt (m : S.Region) : PartialEquiv S.A (Mod k) :=
  OpenPartialHomeomorph.extend (S.dom m) (𝓡∂ (8 + k + 1))

theorem domExt_source (m : S.Region) : (S.domExt m).source = (S.dom m).source :=
  OpenPartialHomeomorph.extend_source (S.dom m)

theorem mem_T_source (m : S.Region) :
    S.domExt m m.1 ∈ (S.T m).source :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.1

theorem T_source_eq_target (m : S.Region) : (S.T m).source = (S.T m).target :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.2.1

theorem T_smooth (m : S.Region) :
    ContDiffOn ℝ ∞ (S.T m : Mod k → Mod k) (S.T m).source :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.2.2.1

theorem T_symm_smooth (m : S.Region) :
    ContDiffOn ℝ ∞ ((S.T m).symm : Mod k → Mod k) (S.T m).target :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.2.2.2.1

theorem sign_iff (m : S.Region) :
    ∀ y ∈ (S.dom m).source,
      S.domExt m y ∈ (S.T m).source →
      (S.Φ y ≤ 0 ↔ 0 ≤ ((S.T m) (S.domExt m y)).ofLp 0) :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.2.2.2.2.2.1

theorem base_coord_zero (m : S.Region) :
    ((S.T m) (S.domExt m m.1)).ofLp 0 = 0 ↔
      (m.1 ∈ (𝓡∂ (8 + k + 1)).boundary S.A ∨ S.Φ m.1 = 0) :=
  (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.2.2.2.2.2.2.1

/-! ## The chart of the region -/

/-- The chart vector of a point of the ambient manifold at the chart of `m`. -/
noncomputable def chartVec (m : S.Region) (w : S.A) : Mod k :=
  S.T m (S.domExt m w)

/-- The source of the chart of the region at `m`. -/
def chartSource (m : S.Region) : Set S.Region :=
  {w : S.Region | w.1 ∈ (S.dom m).source}
    ∩ (fun w : S.Region => S.domExt m w.1) ⁻¹' (S.T m).source

/-- The set of model vectors that are chart values of the source. -/
noncomputable def chartImageSet (m : S.Region) : Set (Mod k) :=
  {v : Mod k | (S.T m).symm v ∈ (S.domExt m).target
    ∧ v ∈ (S.T m).target}

/-- The target of the chart of the region at `m`. -/
noncomputable def chartTarget (m : S.Region) : Set (Half k) :=
  {u : Half k | u.1 ∈ S.chartImageSet m}

/-- The ambient point whose chart vector is `u`. -/
noncomputable def chartInvVal (m : S.Region) (u : Half k) : S.A :=
  (S.domExt m).symm ((S.T m).symm u.1)

theorem chartTarget_eq (m : S.Region) : S.chartTarget m
    = {u : Half k | (S.T m).symm u.1 ∈ (S.domExt m).target
        ∧ u.1 ∈ (S.T m).target} := rfl

theorem isOpen_chartSource (m : S.Region) : IsOpen (S.chartSource m) := by
  rw [chartSource]
  have h1 : IsOpen {w : S.Region | w.1 ∈ (S.dom m).source} :=
    (S.dom m).open_source.preimage continuous_subtype_val
  have hcont : ContinuousOn (fun w : S.Region => S.domExt m w.1)
      {w : S.Region | w.1 ∈ (S.dom m).source} :=
    (S.dom m).continuousOn_extend.comp continuous_subtype_val.continuousOn
      (fun w hw => by rw [OpenPartialHomeomorph.extend_source]; exact hw)
  exact hcont.isOpen_inter_preimage h1 (S.T m).open_source

theorem isOpen_chartTarget (m : S.Region) : IsOpen (S.chartTarget m) := by
  rw [chartTarget_eq]
  exact (Classical.choose_spec (Classical.choose_spec (Work.ThomBordism.exists_chartData_pinned k S m))).2.2.2.2.2.2.1

theorem chartVec_mem_T_target (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    S.chartVec m w.1 ∈ (S.T m).target :=
  (S.T m).map_source hw.2

theorem chartVec_mem_chartImageSet (m : S.Region) {w : S.Region}
    (hw : w ∈ S.chartSource m) : S.chartVec m w.1 ∈ S.chartImageSet m := by
  have hz : (S.T m).symm (S.chartVec m w.1) = S.domExt m w.1 := (S.T m).left_inv hw.2
  refine ⟨?_, S.chartVec_mem_T_target m hw⟩
  rw [hz]
  rw [show (S.domExt m).target = (S.domExt m) '' (S.dom m).source from
    OpenPartialHomeomorph.extend_target_eq_image_source (S.dom m)]
  exact ⟨w.1, hw.1, rfl⟩

theorem chartVec_mem_T_source (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    S.chartVec m w.1 ∈ (S.T m).source := by
  rw [S.T_source_eq_target m]
  exact S.chartVec_mem_T_target m hw

theorem chartVec_nonneg (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    0 ≤ (S.chartVec m w.1).ofLp 0 :=
  ((S.sign_iff m) w.1 hw.1 hw.2).mp w.2

theorem chartInvVal_mem_source (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.chartInvVal m u ∈ (S.dom m).source := by
  have hu' : (S.T m).symm u.1 ∈ (S.domExt m).target ∧ u.1 ∈ (S.T m).target := by
    simpa only [chartTarget, chartImageSet, Set.mem_ofPred_eq] using hu
  have h : S.chartInvVal m u ∈ (S.domExt m).source := PartialEquiv.map_target (S.domExt m) hu'.1
  rwa [S.domExt_source m] at h

theorem chartInvVal_mem_T_source (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.domExt m (S.chartInvVal m u) ∈ (S.T m).source := by
  have hu' : (S.T m).symm u.1 ∈ (S.domExt m).target ∧ u.1 ∈ (S.T m).target := by
    simpa only [chartTarget, chartImageSet, Set.mem_ofPred_eq] using hu
  have h1 : S.domExt m (S.chartInvVal m u) = (S.T m).symm u.1 :=
    PartialEquiv.right_inv _ hu'.1
  rw [h1]
  exact (S.T m).map_target hu'.2

theorem chartVec_chartInvVal (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.chartVec m (S.chartInvVal m u) = u.1 := by
  have hu' : (S.T m).symm u.1 ∈ (S.domExt m).target ∧ u.1 ∈ (S.T m).target := by
    simpa only [chartTarget, chartImageSet, Set.mem_ofPred_eq] using hu
  have h1 : S.domExt m (S.chartInvVal m u) = (S.T m).symm u.1 :=
    PartialEquiv.right_inv _ hu'.1
  rw [chartVec, h1]
  exact (S.T m).right_inv hu'.2

theorem chartInvVal_mem_region (m : S.Region) {u : Half k} (hu : u ∈ S.chartTarget m) :
    S.Φ (S.chartInvVal m u) ≤ 0 := by
  have h := (S.sign_iff m) (S.chartInvVal m u) (S.chartInvVal_mem_source m hu)
    (S.chartInvVal_mem_T_source m hu)
  have h2 : (S.T m) (S.domExt m (S.chartInvVal m u)) = u.1 :=
    S.chartVec_chartInvVal m hu
  rw [h2] at h
  exact h.mpr u.2

/-- **The chart of the region at `m`.** -/
noncomputable def chartAt (m : S.Region) : OpenPartialHomeomorph S.Region (Half k) where
  toFun w := if hw : w ∈ S.chartSource m then
      (⟨S.chartVec m w.1, S.chartVec_nonneg m hw⟩ : Half k)
    else (⟨0, by simp⟩ : Half k)
  invFun u := if hu : u ∈ S.chartTarget m then
      (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
    else m
  source := S.chartSource m
  target := S.chartTarget m
  map_source' w hw := by
    rw [dif_pos hw]
    exact S.chartVec_mem_chartImageSet m hw
  map_target' u hu := by
    rw [dif_pos hu]
    exact ⟨S.chartInvVal_mem_source m hu, S.chartInvVal_mem_T_source m hu⟩
  left_inv' w hw := by
    rw [dif_pos hw]
    have hmem : (⟨S.chartVec m w.1, S.chartVec_nonneg m hw⟩ : Half k) ∈ S.chartTarget m :=
      S.chartVec_mem_chartImageSet m hw
    rw [dif_pos hmem]
    refine Subtype.ext ?_
    have h1 : (S.T m).symm (S.chartVec m w.1)
        = S.domExt m w.1 := (S.T m).left_inv hw.2
    change (S.domExt m).symm
      ((S.T m).symm ((⟨S.chartVec m w.1, S.chartVec_nonneg m hw⟩ : Half k) : Mod k)) = w.1
    rw [h1]
    exact PartialEquiv.left_inv _ (by rw [S.domExt_source m]; exact hw.1)
  right_inv' u hu := by
    rw [dif_pos hu]
    have hmem : (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
        ∈ S.chartSource m :=
      ⟨S.chartInvVal_mem_source m hu, S.chartInvVal_mem_T_source m hu⟩
    rw [dif_pos hmem]
    refine Subtype.ext ?_
    exact S.chartVec_chartInvVal m hu
  open_source := S.isOpen_chartSource m
  open_target := S.isOpen_chartTarget m
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun w : ↥(S.chartSource m) => S.domExt m w.1.1) :=
      (S.dom m).continuousOn_extend.comp_continuous (by fun_prop)
        (fun w => by
          rw [show ((S.dom m).extend (𝓡∂ (8 + k + 1))).source = (S.dom m).source from
            OpenPartialHomeomorph.extend_source (S.dom m)]
          exact w.2.1)
    have h2 : Continuous (fun w : ↥(S.chartSource m) => S.T m (S.domExt m w.1.1)) :=
      (S.T m).continuousOn_toFun.comp_continuous h1
        (fun w => Set.mem_preimage.mp w.2.2)
    have haux : (S.chartSource m).domRestrict (fun w : S.Region =>
        if hw : w ∈ S.chartSource m then
          (⟨S.chartVec m w.1, S.chartVec_nonneg m hw⟩ : Half k)
        else (⟨0, by simp⟩ : Half k))
        = fun w : ↥(S.chartSource m) =>
          (⟨S.chartVec m w.1.1, S.chartVec_nonneg m w.2⟩ : Half k) := by
      funext w
      rw [Set.domRestrict_apply, dif_pos w.2]
    rw [haux]
    exact Continuous.subtype_mk h2 (fun w => S.chartVec_nonneg m w.2)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous (fun u : ↥(S.chartTarget m) => (S.T m).symm u.1.1) :=
      (S.T m).continuousOn_invFun.comp_continuous (by fun_prop)
        (fun u => u.2.2)
    have h2 : Continuous (fun u : ↥(S.chartTarget m) =>
        (S.domExt m).symm ((S.T m).symm u.1.1)) :=
      (S.dom m).continuousOn_extend_symm.comp_continuous h1
        (fun u => u.2.1)
    have haux : (S.chartTarget m).domRestrict (fun u : Half k =>
        if hu : u ∈ S.chartTarget m then
          (⟨S.chartInvVal m u, S.chartInvVal_mem_region m hu⟩ : S.Region)
        else m)
        = fun u : ↥(S.chartTarget m) =>
          (⟨S.chartInvVal m u.1, S.chartInvVal_mem_region m u.2⟩ : S.Region) := by
      funext u
      rw [Set.domRestrict_apply, dif_pos u.2]
    rw [haux]
    exact Continuous.subtype_mk h2 (fun u => S.chartInvVal_mem_region m u.2)

theorem mem_chartSource_self (m : S.Region) : m ∈ S.chartSource m :=
  ⟨S.mem_dom_source m, S.mem_T_source m⟩

theorem chartAt_apply_of_mem (m : S.Region) {w : S.Region} (hw : w ∈ S.chartSource m) :
    S.chartAt m w = (⟨S.chartVec m w.1, S.chartVec_nonneg m hw⟩ : Half k) := by
  change (if hw' : w ∈ S.chartSource m then
      (⟨S.chartVec m w.1, S.chartVec_nonneg m hw'⟩ : Half k)
    else (⟨0, by simp⟩ : Half k)) = _
  rw [dif_pos hw]

/-! ## The transition functions -/

/-- The model-level form of the transition between the charts at `m` and `m'`. -/
noncomputable def transAux (m m' : S.Region) (y : Mod k) : Mod k :=
  S.T m' (S.domExt m' ((S.domExt m).symm ((S.T m).symm y)))

/-- The set on which the model-level transition is defined. -/
def transSource (m m' : S.Region) : Set (Mod k) :=
  {y : Mod k | y ∈ (S.T m).target ∧ (S.T m).symm y
      ∈ ((𝓡∂ (8 + k + 1)).extendCoordChange (S.dom m) (S.dom m')).source
    ∧ S.domExt m' ((S.domExt m).symm ((S.T m).symm y)) ∈ (S.T m').source}

theorem contDiffOn_transAux (m m' : S.Region) :
    ContDiffOn ℝ ∞ (S.transAux m m') (S.transSource m m') := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Mod k => (S.T m).symm y) (S.transSource m m') :=
    (S.T_symm_smooth m).mono (fun y hy => hy.1)
  have h2 : ContDiffOn ℝ ∞ (fun z : Mod k => S.domExt m' ((S.domExt m).symm z))
      (((𝓡∂ (8 + k + 1)).extendCoordChange (S.dom m) (S.dom m')).source) :=
    contDiffOn_extendCoordChange (S.dom_maximalAtlas m) (S.dom_maximalAtlas m')
  have h3 : ContDiffOn ℝ ∞ (fun y : Mod k => S.domExt m' ((S.domExt m).symm ((S.T m).symm y)))
      (S.transSource m m') :=
    h2.comp h1 (fun y hy => hy.2.1)
  have h4 : ContDiffOn ℝ ∞ (fun y : Mod k =>
      S.T m' (S.domExt m' ((S.domExt m).symm ((S.T m).symm y))))
      (S.transSource m m') :=
    (S.T_smooth m').comp h3 (fun y hy => hy.2.2)
  exact h4

end RegionSetupWeak

end

end Work.PTGeometric.WeakRegion
