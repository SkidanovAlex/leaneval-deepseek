import Mathlib
import Submission.Work.ThomBordism.tiedNormalData
import Submission.Work.PTGeometric.exists_localData_at_boundaryZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

/-!
# The tied local datum at a boundary zero

`Submission/Work/ThomBordism/exists_localData_at_boundaryZero_pinned.lean` proves the pointwise
local datum at a boundary zero with the reading map pinned to the frame of an *arbitrary* normal
datum `ND` of the piece embedding.  This file repeats that proof with `ND` replaced by the normal
datum `Work.ThomBordism.tiedND G i` recorded by the `tie` field of `GenuineTubeGeometry` (the one
whose Thom class is `pulledThom`), using
`Work.ThomBordism.exists_model_tube_data_strong_frame_tied` in place of
`Work.ThomBordism.exists_model_tube_data_strong_frame`.  The auxiliary statement lives in its own
namespace so that the final statement keeps the requested form.
-/

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.PTGeometric.WeakRegion

namespace LocalDataTiedAux

theorem exists_localData_at_boundaryZero_tied_aux
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      (Work.PTGeometric.sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (hweak : ∀ y : EuclideanHalfSpace ((8 + k) + 1),
      Work.PTGeometric.sourcePhi G m hpow hphi y = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (Work.PTGeometric.sourcePhi G m hpow hphi) y ≠ 0)
    (hne : ∀ y : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region,
      Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1 ≠ D.t₀)
    (x : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
      (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region)
    (hvx : (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1.1, hne x⟩).2 = 0) :
    ∃ (i : ι) (w0 : (Fam i).pt)
      (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
      (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j)
      (U : Set (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region),
      IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior {y : (Work.PTGeometric.sourceRegionSetup
          (D := D) (Fam := Fam) G m hpow hphi hweak).Region | y.1.1 0 ≤ 1 / 4} ∧
      (∀ y ∈ closure U, ∀ z : Work.PTGeometric.Amb (k + G.mU),
        (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).1 z = z →
        (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU) z = 0 →
        z = 0) ∧
      (∀ y ∈ U, ∀ (hy : y ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
          (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region),
        (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).2 = 0 →
        Manifold.IsSubmersionAt (modelWithCornersEuclideanHalfSpace (8 + k + 1))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region =>
            (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU)
              ((G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).2)) y ∧
        Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k))))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : ↥((modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
            (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region) =>
            (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU)
              ((G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1.1,
                hne y.1⟩).2)) ⟨y, hy⟩) := by
  classical
  haveI : NeZero ((8 + k) + 1) := ⟨by omega⟩
  let S : Work.PTGeometric.WeakRegion.RegionSetupWeak k :=
    Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak
  let Hf : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → D.T :=
    Work.PTGeometric.flatSourceHomotopy8 (k := k)
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ
  let v : S.Region → Amb (k + G.mU) := fun y => (G.coord ⟨Hf y.1.1, hne y⟩).2
  let P : S.Region → EndOp (k + G.mU) := fun y => (G.coord ⟨Hf y.1.1, hne y⟩).1
  -- ### Step 0: `x` is a boundary point of the half space
  have hx0 : x.1.1 0 = 0 := by
    have hcore : Hf x.1.1 ∈ G.core := (G.core_iff_vec ⟨Hf x.1.1, hne x⟩).mpr hvx
    have hmemb : x ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary S.Region := hxb
    rw [S.mem_boundary_iff] at hmemb
    rcases hmemb with h | h
    · exact ((Work.PTGeometric.mem_boundary_halfSpace_iff ((8 + k) + 1)).mp h)
    · exact (Work.PTGeometric.sourcePhi_spec G m hpow hphi).2.2.2.2.1 ⟨hcore, h⟩
  have hcore : Hf x.1.1 ∈ G.core := (G.core_iff_vec ⟨Hf x.1.1, hne x⟩).mpr hvx
  -- ### Step 1: the tube model at `x`
  obtain ⟨i, z, j, hx, ℓf, hpin, W, p, hWopen, hy₀W, hpsm, hptube, hpz, hframe, hℓfinj, hpsurj, hpkill, hcoord⟩ :=
    Work.ThomBordism.exists_model_tube_data_strong_frame_tied (D := D) (Fam := Fam) G m hpow x.1.1 hx0 hcore
  let ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e :=
    Work.ThomBordism.tiedND G i
  -- ### Step 1b: the reading map pinned to the orthonormal frame of the tube normal bundle
  have hℓfinj' : ∀ z' ∈ Work.Tubular.normalSpace (G.emb i) z,
      Work.Tubular.readCLM (G.emb i) ND j z z' = 0 → z' = 0 := by
    simpa only [hpin] using hℓfinj
  let ℓ₀ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Work.Tubular.readCLM (G.emb i) ND j z
  have hℓ₀inj : ∀ z' ∈ Work.Tubular.normalSpace (G.emb i) z, ℓ₀ z' = 0 → z' = 0 := by
    intro z' hz' h0
    exact hℓfinj' z' hz' (show Work.Tubular.readCLM (G.emb i) ND j z z' = 0 from h0)
  -- ### Step 2: the epigraph description of the region at `x`
  obtain ⟨ψ, Wψ, Vψ, hWψopen, htailx, hψsmW, hψnnW, hψ0, hVψopen, hxVψ, hVψsub, hepi⟩ :=
    Work.PTGeometric.exists_epigraph_at_boundaryPoint (D := D) (Fam := Fam) G m hpow hphi x.1 x.2 hx0
  -- ### Step 3: a globally nonnegative variant of `ψ`
  have hVψnn : ∀ z ∈ Vψ, 0 ≤ ψ (tailVec z) := fun z hz => hψnnW (tailVec z) (hVψsub hz)
  let ψv : Mod k → ℝ := fun u => max (ψ u) 0
  have hψv_eq : ∀ z ∈ Vψ, ψv (tailVec z) = ψ (tailVec z) := by
    intro z hz
    show max (ψ (tailVec z)) 0 = ψ (tailVec z)
    exact max_eq_left (hVψnn z hz)
  have hψv_nn : ∀ u : Mod k, 0 ≤ ψv u := fun u => le_max_right _ _
  have hψv_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mod k => ψv (tailVec z)) Vψ :=
    (hψsmW.comp contDiff_tailVec.contDiffOn (fun z hz => hVψsub hz)).congr
      (fun z hz => hψv_eq z hz)
  have hepi' : ∀ (zz : Mod k) (hzV : zz ∈ Vψ) (hz : 0 ≤ zz.ofLp 0),
      (S.Φ ((OpenPartialHomeomorph.refl (Half k)).symm ⟨zz, hz⟩) ≤ 0 ↔
        ψv (tailVec zz) ≤ zz.ofLp 0) := by
    intro zz hzV hz
    have h := hepi zz hzV hz
    rw [← hψv_eq zz hzV] at h
    exact h
  -- ### Step 4: the straightening chart of the region
  obtain ⟨e, he_mem, hxe_src, he_form, he_symm_form⟩ :=
    Work.PTGeometric.regionStraightChart_exists S
      (OpenPartialHomeomorph.refl (Half k))
      (refl_mem_maximalAtlas k) ψv Vψ hVψopen x (Set.mem_univ _) hxVψ hepi' hψv_nn hψv_sm
  -- ### Step 5: the padded linear map
  let ℓ : Amb (k + G.mU) →L[ℝ] Amb k := ℓ₀.comp (projEuc k G.mU G.hmU)
  have hPx : P x = padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i) (p x.1.1)) :=
    congrArg Prod.fst (hcoord x.1.1 hy₀W (hne x))
  have hfootx : tubeFoot (G.emb i) (G.chart i) (p x.1.1) = z := by
    rw [hpz]
    exact tubeFoot_e (G.emb i) (G.chart i) z
  have hinj_x : ∀ zz : Amb (k + G.mU), P x zz = zz → ℓ zz = 0 → zz = 0 := by
    rw [hPx]
    refine padEndEuc_inj_of_fixes (ℓ₀ := ℓ₀) G.hmU
      (tubeNormalProj_mem_Gr (G.emb i) (G.chart i) (p x.1.1)) ?_
    intro w hw hw0
    have hmem : w ∈ Work.Tubular.normalSpace (G.emb i) z := by
      have h1 : w ∈ Work.Tubular.normalSpace (G.emb i)
          (tubeFoot (G.emb i) (G.chart i) (p x.1.1)) := by
        rw [← hw]
        exact tubeNormalProj_apply_mem_normalSpace (G.emb i) (G.chart i) (p x.1.1) w
      rwa [hfootx] at h1
    exact hℓ₀inj w hmem hw0
  -- ### Step 6: continuity of the ambient field
  have hbase : Continuous fun y : S.Region => Hf y.1.1 :=
    (Work.PTGeometric.continuous_flatSourceHomotopy8 k
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcont_coord : Continuous fun y : S.Region =>
      (⟨Hf y.1.1, hne y⟩ : {zz : D.T // zz ≠ D.t₀}) :=
    hbase.subtype_mk (fun y => hne y)
  have hPc : Continuous P := (G.continuous_coord.comp hcont_coord).fst
  -- ### Step 7: the open sets and the neighbourhood `U`
  have hcontval : Continuous fun y : S.Region =>
      (y.1.1 : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hcoord0 : Continuous fun y : S.Region => (y.1.1 0 : ℝ) :=
    ((continuous_apply (0 : Fin ((8 + k) + 1))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((8 + k) + 1) => ℝ)).continuous).comp
      hcontval
  have hUinj_open : IsOpen {y : S.Region | ∀ zz : Amb (k + G.mU), P y zz = zz → ℓ zz = 0 → zz = 0} :=
    isOpen_setOf_injOn_gr ℓ hPc (fun y => G.coord_isProj ⟨Hf y.1.1, hne y⟩)
  have hquarter_open : IsOpen {y : S.Region | y.1.1 0 < 1 / 4} :=
    isOpen_lt hcoord0 continuous_const
  have hW_open : IsOpen {y : S.Region | y.1.1 ∈ W} := hWopen.preimage hcontval
  have hVψ_open : IsOpen {y : S.Region | y.1.1 ∈ Vψ} := hVψopen.preimage hcontval
  let Vall : Set S.Region := {y : S.Region | ∀ zz : Amb (k + G.mU), P y zz = zz → ℓ zz = 0 → zz = 0} ∩
      {y : S.Region | y.1.1 0 < 1 / 4} ∩ {y : S.Region | y.1.1 ∈ W} ∩ {y : S.Region | y.1.1 ∈ Vψ} ∩
      e.source
  have hVall_open : IsOpen Vall :=
    (((hUinj_open.inter hquarter_open).inter hW_open).inter hVψ_open).inter e.open_source
  have hxquarter : x.1.1 0 < 1 / 4 := by rw [hx0]; norm_num
  have hxVall : x ∈ Vall :=
    ⟨⟨⟨⟨hinj_x, hxquarter⟩, hy₀W⟩, hxVψ⟩, hxe_src⟩
  obtain ⟨U, hUopen, hxU, hUcl⟩ :=
    normal_exists_closure_subset (isClosed_singleton (x := x)) hVall_open
      (singleton_subset_iff.mpr hxVall)
  refine ⟨i, z, j, hx, U, hUopen, hxU (Set.mem_singleton x), ?_, ?_, ?_⟩
  · -- the closure stays inside the collar
    refine (hUcl.trans ?_)
    intro y hy
    have hsub : {y : S.Region | y.1.1 0 < 1 / 4} ⊆ {y : S.Region | y.1.1 0 ≤ 1 / 4} := by
      intro zz hz
      have hz' : zz.1.1 0 < 1 / 4 := by simpa using hz
      simpa using le_of_lt hz'
    exact interior_maximal hsub hquarter_open hy.1.1.1.2
  · -- injectivity on the planes
    intro y hy zz hz hz0
    exact (hUcl hy).1.1.1.1 zz hz hz0
  · -- submersivity
    intro y hyU hyb hvy
    have hyUcl : y ∈ closure U := subset_closure hyU
    have hyin : ∀ zz : Amb (k + G.mU), P y zz = zz → ℓ zz = 0 → zz = 0 := (hUcl hyUcl).1.1.1.1
    have hyW : y.1.1 ∈ W := (hUcl hyUcl).1.1.2
    have hyVψ : y.1.1 ∈ Vψ := (hUcl hyUcl).1.2
    have hye : y ∈ e.source := (hUcl hyUcl).2
    have hcoordy := hcoord y.1.1 hyW (hne y)
    have hPy : P y = padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i) (p y.1.1)) :=
      congrArg Prod.fst hcoordy
    have hvy0 : tubeNormalCoord (G.emb i) (G.chart i) (p y.1.1) = 0 := by
      have hs : (G.coord ⟨Hf y.1.1, hne y⟩).2
          = padEuc k G.mU G.hmU (tubeNormalCoord (G.emb i) (G.chart i) (p y.1.1)) :=
        congrArg Prod.snd hcoordy
      have h1 : padEuc k G.mU G.hmU (tubeNormalCoord (G.emb i) (G.chart i) (p y.1.1)) = 0 :=
        hs ▸ hvy
      exact padEuc_injective k G.mU G.hmU (by rw [h1, map_zero])
    have hinj_y : ∀ (x' : (Fam i).pt), (G.emb i).e x' = p y.1.1 →
        ∀ w ∈ Work.Tubular.normalSpace (G.emb i) x', ℓ₀ w = 0 → w = 0 := by
      intro x' hx' w hw hw0
      have hν : Work.Tubular.normalSpace (G.emb i)
          (tubeFoot (G.emb i) (G.chart i) ((G.emb i).e x'))
          = Work.Tubular.normalSpace (G.emb i) x' :=
        tubeNormalProj_normalSpace_e (G.emb i) (G.chart i) x'
      have hfix : tubeNormalProj (G.emb i) (G.chart i) (p y.1.1) w = w := by
        rw [← hx']
        exact tubeNormalProj_fixes_of_mem (G.emb i) (G.chart i) ((G.emb i).e x') w
          (hν.symm ▸ hw)
      have hpad : padEndEuc k G.mU G.hmU (tubeNormalProj (G.emb i) (G.chart i) (p y.1.1))
          (padEuc k G.mU G.hmU w) = padEuc k G.mU G.hmU w := by
        rw [padEndEuc_apply, projEuc_padEuc, hfix]
      have hℓpad : ℓ (padEuc k G.mU G.hmU w) = 0 := by
        show ℓ₀ (projEuc k G.mU G.hmU (padEuc k G.mU G.hmU w)) = 0
        rw [projEuc_padEuc, hw0]
      have h0 := hyin (padEuc k G.mU G.hmU w) (by rw [hPy]; exact hpad) hℓpad
      exact padEuc_injective k G.mU G.hmU (by rw [h0, map_zero])
    have hsurj_y : Function.Surjective
        (fderiv ℝ (fun zz : Mod k => ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p zz))) y.1.1) :=
      Work.PTGeometric.fderiv_tubeCoord_surjective (G.emb i) (G.chart i) ℓ₀ hWopen hpsm hpsurj hyW
        (hptube y.1.1 hyW) hvy0 hinj_y
    let Gfun : Mod k → Amb k := fun zz => ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p zz))
    let gfun : Mod k → Amb k :=
      fun u => ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p (unstrAux ψv u)))
    have hGfun_surj : Function.Surjective (fderiv ℝ Gfun y.1.1) := hsurj_y
    -- differentiability of `Gfun`
    have hp_diff : HasFDerivAt p (fderiv ℝ p y.1.1) y.1.1 :=
      ((hpsm.contDiffAt (hWopen.mem_nhds hyW)).differentiableAt (by simp)).hasFDerivAt
    have htnc_diff : HasFDerivAt (tubeNormalCoord (G.emb i) (G.chart i))
        (fderiv ℝ (tubeNormalCoord (G.emb i) (G.chart i)) (p y.1.1)) (p y.1.1) := by
      have hcd := (contMDiffOn_iff_contDiffOn).mp
        (Work.PTGeometric.contMDiffOn_tubeNormalCoord (G.emb i) (G.chart i))
      exact ((hcd.contDiffAt ((G.chart i).openTube_isOpen.mem_nhds (hptube y.1.1 hyW))).differentiableAt
        (by simp)).hasFDerivAt
    have hGfun_full : HasFDerivAt Gfun
        (ℓ₀.comp ((fderiv ℝ (tubeNormalCoord (G.emb i) (G.chart i)) (p y.1.1)).comp
          (fderiv ℝ p y.1.1))) y.1.1 :=
      (ContinuousLinearMap.hasFDerivAt ℓ₀).comp y.1.1 (htnc_diff.comp y.1.1 hp_diff)
    have hGfun_diff : HasFDerivAt Gfun (fderiv ℝ Gfun y.1.1) y.1.1 :=
      hGfun_full.fderiv.symm ▸ hGfun_full
    have hGfun_eZero : (fderiv ℝ Gfun y.1.1) eZero = 0 := by
      rw [hGfun_full.fderiv]
      show ℓ₀ ((fderiv ℝ (tubeNormalCoord (G.emb i) (G.chart i)) (p y.1.1))
        ((fderiv ℝ p y.1.1) eZero)) = 0
      have hp0 : (fderiv ℝ p y.1.1) eZero = 0 := hpkill y.1.1 hyW
      rw [hp0, map_zero, map_zero]
    -- smoothness of the inverse straightening
    have hψvtail_sm : ContDiffOn ℝ ∞ (fun z : Mod k => ψv (tailVec z)) (tailVec ⁻¹' Wψ) :=
      (hψsmW.comp contDiff_tailVec.contDiffOn (fun z hz => hz)).congr
        (fun z hz => by
          show max (ψ (tailVec z)) 0 = ψ (tailVec z)
          exact max_eq_left (hψnnW (tailVec z) hz))
    have hunstrAux_sm : ContDiffOn ℝ ∞ (unstrAux ψv) (tailVec ⁻¹' Wψ) := by
      have h1 : ContDiffOn ℝ ∞ (fun u : Mod k => u + ψv (tailVec u) • eZero) (tailVec ⁻¹' Wψ) :=
        ContDiffOn.add contDiffOn_id (ContDiffOn.smul hψvtail_sm contDiffOn_const)
      refine h1.congr ?_
      intro u _
      exact unstrAux_eq_add_smul_eZero ψv u
    -- the base point of the chart
    have hu₀ : (e.extend (𝓡∂ (8 + k + 1))) y = strAux ψv y.1.1 := by
      have h1 : (e.extend (𝓡∂ (8 + k + 1))) y = (e y).1 := by
        rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
          modelWithCornersEuclideanHalfSpace_apply]
      have h2 : (e y).1 = strAux ψv y.1.1 := he_form y hye
      rw [h1, h2]
    have hg_unstr : unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y) = y.1.1 := by
      rw [hu₀, unstrAux_strAux]
    have hu₀W : unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y) ∈ W := by
      rw [hg_unstr]
      exact hyW
    have hu₀tail : tailVec ((e.extend (𝓡∂ (8 + k + 1))) y) ∈ Wψ := by
      rw [hu₀, tailVec_strAux]
      exact hVψsub hyVψ
    have hunstrAux_contAt : ContinuousAt (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      (hunstrAux_sm.contDiffAt ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)).continuousAt
    have hunstrAux_diff : DifferentiableAt ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      (hunstrAux_sm.differentiableOn (by simp)).differentiableAt
        ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)
    have hψvtail_diff : DifferentiableAt ℝ (fun z : Mod k => ψv (tailVec z))
        ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      (hψvtail_sm.differentiableOn (by simp)).differentiableAt
        ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)
    -- ### the model function
    have hgg : ∃ Ug ∈ 𝓝 ((e.extend (𝓡∂ (8 + k + 1))) y), ContDiffOn ℝ ∞ gfun Ug := by
      refine ⟨(tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W), Filter.inter_mem
        ((hWψopen.preimage continuous_tailVec).mem_nhds hu₀tail)
        (hunstrAux_contAt.preimage_mem_nhds (hWopen.mem_nhds hu₀W)), ?_⟩
      have h1 : ContDiffOn ℝ ∞ (unstrAux ψv) ((tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W)) :=
        hunstrAux_sm.mono (fun u hu => hu.1)
      have h2 : ContDiffOn ℝ ∞ (fun u => p (unstrAux ψv u))
          ((tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W)) :=
        hpsm.comp h1 (fun u hu => hu.2)
      have h3 : ContDiffOn ℝ ∞ (fun u => tubeNormalCoord (G.emb i) (G.chart i) (p (unstrAux ψv u)))
          ((tailVec ⁻¹' Wψ) ∩ (unstrAux ψv ⁻¹' W)) :=
        ((contMDiffOn_iff_contDiffOn).mp
          (Work.PTGeometric.contMDiffOn_tubeNormalCoord (G.emb i) (G.chart i))).comp h2
          (fun u hu => hptube _ hu.2)
      exact (ℓ₀.contDiff.contDiffOn).comp h3 (fun _ _ => Set.mem_univ _)
    -- ### the chain rule
    have hGfun_diff' : HasFDerivAt Gfun (fderiv ℝ Gfun y.1.1)
        (unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y)) := by
      rw [hg_unstr]
      exact hGfun_diff
    have hgfun_diff : HasFDerivAt gfun
        ((fderiv ℝ Gfun y.1.1).comp (fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)))
        ((e.extend (𝓡∂ (8 + k + 1))) y) :=
      hGfun_diff'.comp _ hunstrAux_diff.hasFDerivAt
    have hgfun_fderiv : fderiv ℝ gfun ((e.extend (𝓡∂ (8 + k + 1))) y)
        = (fderiv ℝ Gfun y.1.1).comp (fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)) :=
      hgfun_diff.fderiv
    have hsurjg : Function.Surjective (fderiv ℝ gfun ((e.extend (𝓡∂ (8 + k + 1))) y)) := by
      rw [hgfun_fderiv]
      show Function.Surjective ((fderiv ℝ Gfun y.1.1)
        ∘ (fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)))
      exact Function.Surjective.comp hGfun_surj (surjective_fderiv_unstrAux ψv hψvtail_diff)
    have hnormg : ∃ vv : Mod k, (fderiv ℝ gfun ((e.extend (𝓡∂ (8 + k + 1))) y)) vv = 0 ∧ vv 0 ≠ 0 := by
      refine ⟨eZero, ?_, by rw [eZero_apply]; norm_num⟩
      rw [hgfun_fderiv]
      show (fderiv ℝ Gfun y.1.1)
        ((fderiv ℝ (unstrAux ψv) ((e.extend (𝓡∂ (8 + k + 1))) y)) eZero) = 0
      rw [fderiv_unstrAux_eZero ψv _ hunstrAux_diff, hGfun_eZero]
    -- ### the agreement of the two maps near `y`
    have hagree : (fun y' : S.Region => ℓ (v y')) =ᶠ[𝓝 y]
        (fun y' : S.Region => gfun ((e.extend (𝓡∂ (8 + k + 1))) y')) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨e.source ∩ {y' : S.Region | y'.1.1 ∈ W}, ?_, ?_⟩
      · exact Filter.inter_mem (e.open_source.mem_nhds hye) (hW_open.mem_nhds hyW)
      · intro y' hy'
        rcases hy' with ⟨hy'e, hy'W⟩
        have h1 : (e.extend (𝓡∂ (8 + k + 1))) y' = strAux ψv y'.1.1 := by
          have h1a : (e.extend (𝓡∂ (8 + k + 1))) y' = (e y').1 := by
            rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
              modelWithCornersEuclideanHalfSpace_apply]
          have h1b : (e y').1 = strAux ψv y'.1.1 := he_form y' hy'e
          rw [h1a, h1b]
        have h2 : gfun ((e.extend (𝓡∂ (8 + k + 1))) y')
            = ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) := by
          show ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i)
            (p (unstrAux ψv ((e.extend (𝓡∂ (8 + k + 1))) y')))) = _
          rw [h1, unstrAux_strAux]
        have hv' : v y' = padEuc k G.mU G.hmU
            (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) :=
          congrArg Prod.snd (hcoord y'.1.1 hy'W (hne y'))
        have h3 : ℓ (v y') = ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) := by
          calc ℓ (v y') = ℓ₀ (projEuc k G.mU G.hmU (v y')) := rfl
            _ = ℓ₀ (projEuc k G.mU G.hmU (padEuc k G.mU G.hmU
                  (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)))) := by rw [hv']
            _ = ℓ₀ (tubeNormalCoord (G.emb i) (G.chart i) (p y'.1.1)) := by rw [projEuc_padEuc]
        show ℓ (v y') = gfun ((e.extend (𝓡∂ (8 + k + 1))) y')
        rw [h2, h3]
    exact isSubmersionAt_and_boundary_of_chartModel (n := 8 + k) he_mem hye hyb hgg hagree hsurjg hnormg

end LocalDataTiedAux

end

end Work.PTGeometric

namespace Work.ThomBordism

/-- The pointwise local datum at a boundary zero, with the prescribed chart pinned to the frame
coordinates of the *tied* normal data `Work.ThomBordism.tiedND G i` (the normal datum recorded by the
tie field of `GenuineTubeGeometry`, the one whose Thom class is `pulledThom`).

This is verbatim `Work.ThomBordism.exists_localData_at_boundaryZero_pinned`
(`Submission/Work/ThomBordism/exists_localData_at_boundaryZero_pinned.lean`) with the existential
normal datum `(ND : NormalData ...)` replaced by `Work.ThomBordism.tiedND G i`, so the proof is that
file's proof of `Work.PTGeometric.exists_localData_at_boundaryZero_pinned_aux` with
`Work.ThomBordism.exists_model_tube_data_strong_frame` replaced by
`Work.ThomBordism.exists_model_tube_data_strong_frame_tied`
(`Submission/Work/ThomBordism/tiedNormalData.lean`), `ND` becoming the `let`-bound abbreviation
`Work.ThomBordism.tiedND G i` and the `obtain` line dropping `ND` from its tuple: only the
injectivity of the reading map on the normal space at the foot (which holds for any normal datum)
and `hpin` are used.  A useful blueprint: copy
`Work.PTGeometric.exists_localData_at_boundaryZero_pinned_aux`'s proof, but with
`Work.ThomBordism.exists_model_tube_data_strong_frame` replaced by
`Work.ThomBordism.exists_model_tube_data_strong_frame_tied` (whose tuple is `i, z, j, hx, ℓ, hpin, W,
p, …`, i.e. `ND` is no longer a member) and with `let ND : NormalData (Fam i) k (G.emb i).e :=
Work.ThomBordism.tiedND G i` inserted directly after that `obtain`.  `set_option maxHeartbeats
3200000` is required. -/
theorem localDataTied
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G m hpow)
      (Work.PTGeometric.sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (hweak : ∀ y : EuclideanHalfSpace ((8 + k) + 1),
      Work.PTGeometric.sourcePhi G m hpow hphi y = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (Work.PTGeometric.sourcePhi G m hpow hphi) y ≠ 0)
    (hne : ∀ y : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region,
      Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1 ≠ D.t₀)
    (x : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region)
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
      (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region)
    (hvx : (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ x.1.1, hne x⟩).2 = 0) :
    ∃ (i : ι) (w0 : (Fam i).pt)
      (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
      (hb : w0 ∈ (Work.ThomBordism.tiedND G i).D.baseSet j)
      (U : Set (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region),
      IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior {y : (Work.PTGeometric.sourceRegionSetup
          (D := D) (Fam := Fam) G m hpow hphi hweak).Region | y.1.1 0 ≤ 1 / 4} ∧
      (∀ y ∈ closure U, ∀ z : Work.PTGeometric.Amb (k + G.mU),
        (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).1 z = z →
        (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU) z = 0 →
        z = 0) ∧
      (∀ y ∈ U, ∀ (hy : y ∈ (modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
          (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region),
        (G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).2 = 0 →
        Manifold.IsSubmersionAt (modelWithCornersEuclideanHalfSpace (8 + k + 1))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region =>
            (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU)
              ((G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1, hne y⟩).2)) y ∧
        Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k))))
          (modelWithCornersSelf ℝ (Work.PTGeometric.Amb k)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : ↥((modelWithCornersEuclideanHalfSpace (8 + k + 1)).boundary
            (Work.PTGeometric.sourceRegionSetup (D := D) (Fam := Fam) G m hpow hphi hweak).Region) =>
            (Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j w0).comp (Work.PTGeometric.projEuc k G.mU G.hmU)
              ((G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
              (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y.1.1.1,
                hne y.1⟩).2)) ⟨y, hy⟩) := by
  exact Work.PTGeometric.LocalDataTiedAux.exists_localData_at_boundaryZero_tied_aux
    G m hpow hphi hweak hne x hxb hvx

end Work.ThomBordism
