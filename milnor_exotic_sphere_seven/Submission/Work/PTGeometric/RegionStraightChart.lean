import Mathlib
import Submission.Work.PTGeometric.RegionStraightBasic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric

noncomputable section

variable {k : ℕ}

def chartSrc (S : WeakRegion.RegionSetupWeak k) (φ : OpenPartialHomeomorph S.A (Half k))
    (V : Set (Mod k)) : Set S.Region :=
  {w | w.1 ∈ φ.source ∧ (φ w.1).1 ∈ V}

def φTgt (S : WeakRegion.RegionSetupWeak k) (φ : OpenPartialHomeomorph S.A (Half k)) :
    Set (Mod k) :=
  {z | ∃ hz : 0 ≤ z.ofLp 0, (⟨z, hz⟩ : Half k) ∈ φ.target}

def chartTgt (S : WeakRegion.RegionSetupWeak k) (φ : OpenPartialHomeomorph S.A (Half k))
    (ψ : Mod k → ℝ) (V : Set (Mod k)) : Set (Half k) :=
  {u | unstrAux ψ u.1 ∈ V ∧ unstrAux ψ u.1 ∈ φTgt S φ}

theorem half_ext {z : Mod k} {h1 h2 : 0 ≤ z.ofLp 0} :
    (⟨z, h1⟩ : Half k) = ⟨z, h2⟩ := Subtype.ext rfl

theorem mem_chartSrc_iff {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {V : Set (Mod k)} {w : S.Region} :
    w ∈ chartSrc S φ V ↔ w.1 ∈ φ.source ∧ (φ w.1).1 ∈ V := Iff.rfl

theorem mem_φTgt_iff {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {z : Mod k} :
    z ∈ φTgt S φ ↔ ∃ hz : 0 ≤ z.ofLp 0, (⟨z, hz⟩ : Half k) ∈ φ.target := Iff.rfl

theorem mem_chartTgt_iff {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {ψ : Mod k → ℝ} {V : Set (Mod k)}
    {u : Half k} :
    u ∈ chartTgt S φ ψ V ↔ unstrAux ψ u.1 ∈ V ∧ unstrAux ψ u.1 ∈ φTgt S φ := Iff.rfl

section

variable {S : WeakRegion.RegionSetupWeak k} {φ : OpenPartialHomeomorph S.A (Half k)}
  {ψ : Mod k → ℝ} {V : Set (Mod k)}

theorem phi_symm_phi {y : S.A} (hy : y ∈ φ.source) : φ.symm (φ y) = y :=
  PartialEquiv.left_inv (φ.toPartialEquiv) hy

theorem phi_phi_symm {y : Half k} (hy : y ∈ φ.target) : φ (φ.symm y) = y :=
  PartialEquiv.right_inv (φ.toPartialEquiv) hy

theorem chartSrc_nonneg
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    {w : S.Region} (hw : w ∈ chartSrc S φ V) :
    0 ≤ (strAux ψ (φ w.1).1).ofLp 0 := by
  rw [strAux_eq, ofLp_sub_smul_eZero]
  have hz := (φ w.1).2
  have hle := (hepi (φ w.1).1 hw.2 hz).mp ?_
  · linarith
  · have hhalf : (⟨(φ w.1).1, hz⟩ : Half k) = φ w.1 := rfl
    rw [hhalf, phi_symm_phi (φ := φ) hw.1]
    exact w.2

theorem chartTgt_mem_region
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    (hψnn : ∀ u : Mod k, 0 ≤ ψ u) {u : Half k} (hu : u ∈ chartTgt S φ ψ V) :
    S.Φ (φ.symm (⟨unstrAux ψ u.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k))
      ≤ 0 := by
  have h1 : unstrAux ψ u.1 ∈ V := hu.1
  refine (hepi (unstrAux ψ u.1) h1
    (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u))).mpr ?_
  rw [unstrAux_eq, tailVec_add_smul_eZero, ofLp_add_smul_eZero]
  linarith [u.2]

theorem half_ext_choose {z : Mod k} (h : z ∈ φTgt S φ)
    (h2 : 0 ≤ z.ofLp 0) :
    (⟨z, h2⟩ : Half k) ∈ φ.target := by
  rw [half_ext (h1 := h2) (h2 := Classical.choose h)]
  exact Classical.choose_spec h

theorem regionChart_val_mem_tgt
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    {w : S.Region} (hw : w ∈ chartSrc S φ V) :
    (⟨strAux ψ (φ w.1).1,
      chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw⟩ : Half k)
      ∈ chartTgt S φ ψ V := by
  refine ⟨?_, ?_⟩
  · rw [unstrAux_strAux]
    exact hw.2
  · rw [unstrAux_strAux]
    refine ⟨(φ w.1).2, ?_⟩
    have hhalf : (⟨(φ w.1).1, (φ w.1).2⟩ : Half k) = φ w.1 := rfl
    rw [hhalf]
    exact φ.map_source hw.1

theorem regionChart_inv_mem_src
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    (hψnn : ∀ u : Mod k, 0 ≤ ψ u) {u : Half k} (hu : u ∈ chartTgt S φ ψ V) :
    (⟨φ.symm (⟨unstrAux ψ u.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k),
      chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu⟩ : S.Region)
      ∈ chartSrc S φ V := by
  have hz0 : 0 ≤ (unstrAux ψ u.1).ofLp 0 := unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)
  have hT : (⟨unstrAux ψ u.1, hz0⟩ : Half k) ∈ φ.target := half_ext_choose hu.2 hz0
  refine ⟨φ.map_target hT, ?_⟩
  have h1 : φ (φ.symm (⟨unstrAux ψ u.1, hz0⟩ : Half k)) = ⟨unstrAux ψ u.1, hz0⟩ :=
    phi_phi_symm (φ := φ) hT
  show (φ (φ.symm (⟨unstrAux ψ u.1, hz0⟩ : Half k))).1 ∈ V
  rw [h1]
  exact hu.1

theorem isOpen_chartSrc (hV : IsOpen V) : IsOpen (chartSrc S φ V) := by
  have h1 : IsOpen {w : S.Region | w.1 ∈ φ.source} := φ.open_source.preimage continuous_subtype_val
  have hA : ContinuousOn (fun w : S.Region => φ w.1) {w : S.Region | w.1 ∈ φ.source} :=
    φ.continuousOn_toFun.comp continuous_subtype_val.continuousOn (fun w hw => hw)
  have hcont : ContinuousOn (fun w : S.Region => (φ w.1).1) {w : S.Region | w.1 ∈ φ.source} :=
    (continuousOn_univ.mpr continuous_subtype_val).comp hA (fun w _ => trivial)
  have h2 : IsOpen ({w : S.Region | w.1 ∈ φ.source}
      ∩ (fun w : S.Region => (φ w.1).1) ⁻¹' V) :=
    hcont.isOpen_inter_preimage h1 hV
  have hset : chartSrc S φ V = {w : S.Region | w.1 ∈ φ.source}
      ∩ (fun w : S.Region => (φ w.1).1) ⁻¹' V := by
    ext w; rfl
  rw [hset]; exact h2

theorem subset_chartTgt_satSet {u : Half k} (hu : u ∈ chartTgt S φ ψ V) :
    u.1 ∈ satSet V := by
  rw [mem_satSet_iff]
  exact ⟨unstrAux ψ u.1, hu.1, by rw [tailVec_unstrAux]⟩

theorem preimage_chartTgt_eq (hψnn : ∀ u : Mod k, 0 ≤ ψ u) :
    chartTgt S φ ψ V = {u : Half k | u.1 ∈ satSet V}
        ∩ (fun u : Half k => unstrAux ψ u.1) ⁻¹' V
        ∩ (fun u : Half k =>
            (⟨unstrAux ψ u.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k))
          ⁻¹' φ.target := by
  ext u
  rw [mem_chartTgt_iff]
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨subset_chartTgt_satSet ⟨h1, h2⟩, h1⟩,
      half_ext_choose h2 (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u))⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨h1, ⟨unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u), h2⟩⟩

theorem isOpen_chartTgt (hV : IsOpen V) (hψnn : ∀ u : Mod k, 0 ≤ ψ u)
    (hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V) : IsOpen (chartTgt S φ ψ V) := by
  have hU : IsOpen {u : Half k | u.1 ∈ satSet V} :=
    (isOpen_satSet hV).preimage continuous_subtype_val
  have hFU : ContinuousOn (fun u : Half k => unstrAux ψ u.1) {u : Half k | u.1 ∈ satSet V} :=
    (contDiffOn_unstrAux_satSet hV hψsm).continuousOn.comp continuous_subtype_val.continuousOn
      (fun u hu => hu)
  have hGU : ContinuousOn (fun u : Half k =>
      (⟨unstrAux ψ u.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k))
      {u : Half k | u.1 ∈ satSet V} := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.subtype_mk ?_ _
    exact hFU.comp_continuous continuous_subtype_val (fun u => u.2)
  rw [preimage_chartTgt_eq (S := S) (φ := φ) (ψ := ψ) (V := V) hψnn]
  have hAB := hFU.isOpen_inter_preimage hU hV
  have hAC := hGU.isOpen_inter_preimage hU φ.open_target
  convert hAB.inter hAC using 1
  ext u
  simp only [mem_inter_iff, mem_preimage]
  tauto

/-- **The straightening chart of the region.** -/
noncomputable def regionChart (S : WeakRegion.RegionSetupWeak k)
    (φ : OpenPartialHomeomorph S.A (Half k)) (ψ : Mod k → ℝ) (V : Set (Mod k))
    (hV : IsOpen V)
    (hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0))
    (hψnn : ∀ u : Mod k, 0 ≤ ψ u)
    (hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V)
    (x : S.Region) (hxsrc : x.1 ∈ φ.source) (hxV : (φ x.1).1 ∈ V) :
    OpenPartialHomeomorph S.Region (Half k) where
  toFun w := if hw : w ∈ chartSrc S φ V then
      (⟨strAux ψ (φ w.1).1,
        chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw⟩ : Half k)
    else (⟨0, by simp [PiLp.zero_apply]⟩ : Half k)
  invFun u := if hu : u ∈ chartTgt S φ ψ V then
      (⟨φ.symm (⟨unstrAux ψ u.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k),
        chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu⟩ : S.Region)
    else x
  source := chartSrc S φ V
  target := chartTgt S φ ψ V
  map_source' w hw := by
    rw [dif_pos hw]
    exact regionChart_val_mem_tgt (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw
  map_target' u hu := by
    rw [dif_pos hu]
    exact regionChart_inv_mem_src (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu
  left_inv' w hw := by
    rw [dif_pos hw]
    rw [dif_pos (regionChart_val_mem_tgt (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw)]
    refine Subtype.ext ?_
    convert phi_symm_phi (φ := φ) hw.1
    exact Subtype.ext (unstrAux_strAux ψ (φ w.1).1)
  right_inv' u hu := by
    rw [dif_pos hu]
    rw [dif_pos (regionChart_inv_mem_src (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu)]
    refine Subtype.ext ?_
    have hz0 : 0 ≤ (unstrAux ψ u.1).ofLp 0 := unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)
    have hT : (⟨unstrAux ψ u.1, hz0⟩ : Half k) ∈ φ.target := half_ext_choose hu.2 hz0
    have h1 : φ (φ.symm (⟨unstrAux ψ u.1, hz0⟩ : Half k)) = ⟨unstrAux ψ u.1, hz0⟩ :=
      phi_phi_symm (φ := φ) hT
    show strAux ψ ((φ (φ.symm (⟨unstrAux ψ u.1, hz0⟩ : Half k))).1) = u.1
    rw [h1, strAux_unstrAux]
  open_source := isOpen_chartSrc (S := S) (φ := φ) (V := V) hV
  open_target := isOpen_chartTgt (S := S) (φ := φ) (ψ := ψ) (V := V) hV hψnn hψsm
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hsub : Continuous (fun w : ↥(chartSrc S φ V) => (w.1 : S.A)) := by fun_prop
    have hB : Continuous (fun w : ↥(chartSrc S φ V) => (φ w.1.1).1) :=
      (continuousOn_univ.mpr continuous_subtype_val).comp_continuous
        (φ.continuousOn_toFun.comp_continuous hsub (fun w => w.2.1)) (fun _ => trivial)
    have hC : Continuous (fun w : ↥(chartSrc S φ V) => ψ (tailVec (φ w.1.1).1)) :=
      (contDiffOn_psi_tailVec_satSet hV hψsm).continuousOn.comp_continuous hB
        (fun w => subset_satSet V w.2.2)
    have hD : Continuous (fun w : ↥(chartSrc S φ V) => strAux ψ (φ w.1.1).1) := by
      have h1 : Continuous (fun w : ↥(chartSrc S φ V) =>
          ψ (tailVec (φ w.1.1).1) • (eZero : Mod k)) :=
        hC.smul continuous_const
      refine (hB.sub h1).congr fun w => ?_
      simp only [Pi.sub_apply]
      rw [strAux_eq]
    have haux : (chartSrc S φ V).domRestrict (fun w : S.Region =>
        if hw : w ∈ chartSrc S φ V then
          (⟨strAux ψ (φ w.1).1,
            chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw⟩ : Half k)
        else (⟨0, by simp [PiLp.zero_apply]⟩ : Half k))
        = fun w : ↥(chartSrc S φ V) =>
          (⟨strAux ψ (φ w.1.1).1,
            chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi w.2⟩ : Half k) := by
      funext w
      rw [Set.domRestrict_apply, dif_pos w.2]
    rw [haux]
    exact Continuous.subtype_mk hD _
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hV' : Continuous (fun u : ↥(chartTgt S φ ψ V) => u.1.1) := by fun_prop
    have hW : Continuous (fun u : ↥(chartTgt S φ ψ V) => ψ (tailVec u.1.1)) :=
      (contDiffOn_psi_tailVec_satSet hV hψsm).continuousOn.comp_continuous hV'
        (fun u => subset_chartTgt_satSet u.2)
    have hU : Continuous (fun u : ↥(chartTgt S φ ψ V) => unstrAux ψ u.1.1) := by
      have h1 : Continuous (fun u : ↥(chartTgt S φ ψ V) =>
          ψ (tailVec u.1.1) • (eZero : Mod k)) := hW.smul continuous_const
      refine (hV'.add h1).congr fun u => ?_
      simp only [Pi.add_apply]
      rw [unstrAux_eq]
    have hhalf : Continuous (fun u : ↥(chartTgt S φ ψ V) =>
        (⟨unstrAux ψ u.1.1, unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u.1)⟩ : Half k)) :=
      hU.subtype_mk _
    have hphi : Continuous (fun u : ↥(chartTgt S φ ψ V) =>
        φ.symm (⟨unstrAux ψ u.1.1,
          unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u.1)⟩ : Half k)) :=
      φ.continuousOn_symm.comp_continuous hhalf
        (fun u => half_ext_choose u.2.2 (unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u.1)))
    have haux : (chartTgt S φ ψ V).domRestrict (fun u : Half k =>
        if hu : u ∈ chartTgt S φ ψ V then
          (⟨φ.symm (⟨unstrAux ψ u.1,
              unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k),
            chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu⟩ : S.Region)
        else x)
        = fun u : ↥(chartTgt S φ ψ V) =>
          (⟨φ.symm (⟨unstrAux ψ u.1.1,
              unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u.1)⟩ : Half k),
            chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn u.2⟩ : S.Region) := by
      funext u
      rw [Set.domRestrict_apply, dif_pos u.2]
    rw [haux]
    exact Continuous.subtype_mk hphi _

/-- The value of the straightening chart on its source. -/
theorem regionChart_apply_of_mem {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {ψ : Mod k → ℝ} {V : Set (Mod k)}
    {hV : IsOpen V}
    {hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0)}
    {hψnn : ∀ u : Mod k, 0 ≤ ψ u}
    {hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V}
    {x : S.Region} {hxsrc : x.1 ∈ φ.source} {hxV : (φ x.1).1 ∈ V}
    {w : S.Region} (hw : w ∈ chartSrc S φ V) :
    regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV w
      = (⟨strAux ψ (φ w.1).1,
          chartSrc_nonneg (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hw⟩ : Half k) :=
  dif_pos hw

/-- The value of the inverse of the straightening chart on its target. -/
theorem regionChart_symm_apply_of_mem {S : WeakRegion.RegionSetupWeak k}
    {φ : OpenPartialHomeomorph S.A (Half k)} {ψ : Mod k → ℝ} {V : Set (Mod k)}
    {hV : IsOpen V}
    {hepi : ∀ (z : Mod k), z ∈ V → ∀ (hz : 0 ≤ z.ofLp 0),
      (S.Φ (φ.symm ⟨z, hz⟩) ≤ 0 ↔ ψ (tailVec z) ≤ z.ofLp 0)}
    {hψnn : ∀ u : Mod k, 0 ≤ ψ u}
    {hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V}
    {x : S.Region} {hxsrc : x.1 ∈ φ.source} {hxV : (φ x.1).1 ∈ V}
    {u : Half k} (hu : u ∈ chartTgt S φ ψ V) :
    (regionChart S φ ψ V hV hepi hψnn hψsm x hxsrc hxV).symm u
      = (⟨φ.symm (⟨unstrAux ψ u.1,
            unstrAux_mem_halfSpace (ψ := ψ) hψnn (z := u)⟩ : Half k),
          chartTgt_mem_region (S := S) (φ := φ) (ψ := ψ) (V := V) hepi hψnn hu⟩ : S.Region) :=
  dif_pos hu

end

end

end Work.PTGeometric
