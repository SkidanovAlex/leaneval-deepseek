import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs
import Submission.Work.ThomBordism.LeadChapter.TubeDetCore
import Submission.Work.PTGeometric.exists_model_submersion_at_mem_core
import Submission.Work.ThomBordism.KeyLocal.gmTubeProductAux
import Submission.Work.ThomBordism.LeadChapter.thetaInvAux
import Submission.Work.ThomBordism.range_ogFrameCLM
import Submission.Work.PTGeometric.contMDiff_normalProjCLM
import Submission.Work.PTGeometric.exists_localData_at_boundaryZero
import Submission.Work.PTGeometric.fderiv_normalCoord_eq_tubeNormalProj
import Submission.Work.ThomBordism.LeadChapter.vSrcEventualModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.LeadChapter.tubeDetKernel`

The kernel/range statement of the collar chart of the level set: the derivative of the raw level
function `vSrc` at a collar point has kernel the image of the block frame `[∂_t | dΞ]`, and any
normal frame `N` realising the Gauss frame agrees with `frameN` modulo that image.

No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open CategoryTheory

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-! ## §1  The injectivity of the block frame -/

/-- The spatial embedding `srcOfSpatial` is injective. -/
theorem srcOfSpatial_injective (k : ℕ) : Function.Injective (srcOfSpatial k) := by
  intro v w h
  rw [← tail_srcCast_srcOfSpatial k v, ← tail_srcCast_srcOfSpatial k w, h]

/-- **The block frame in coordinates**: `[∂_t | dΞ]` adds the collar direction `e₀` to the spatial
frame. -/
theorem collarB_apply (k : ℕ)
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (x : Work.ThomBordism.CofAtlas.E9) :
    collarB k A x = srcOfSpatial k (A (tail 8 x)) + (x 0) • eZero := by
  rw [collarB]
  simp only [add_apply, ContinuousLinearMap.comp_apply, srcOfSpatialCLM_apply, collarCLM_apply]
  rfl

/-- **The block frame is injective** as soon as the spatial part is. -/
theorem collarB_injective {k : ℕ}
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (hA : Function.Injective A) : Function.Injective (collarB k A) := by
  intro x y hxy
  have hxy' : srcOfSpatial k (A (tail 8 x)) + (x 0) • eZero
      = srcOfSpatial k (A (tail 8 y)) + (y 0) • eZero := by
    rw [← collarB_apply, ← collarB_apply]; exact hxy
  have h0 : x 0 = y 0 := by
    have h := congrArg (fun w : Work.ThomBordism.CofAtlas.ModN k => w 0) hxy'
    simp only [PiLp.add_apply, PiLp.smul_apply, srcOfSpatial_zero, zero_add,
      eZero_apply, smul_eq_mul, mul_one] at h
    exact h
  have hsrc : srcOfSpatial k (A (tail 8 x)) = srcOfSpatial k (A (tail 8 y)) := by
    rw [h0] at hxy'
    exact add_right_cancel hxy'
  have htail : tailCLM 8 x = tailCLM 8 y := hA (srcOfSpatial_injective k hsrc)
  rw [← consCLM_tail 8 x, ← consCLM_tail 8 y, h0, htail]

/-- The derivative of the chart representative of the embedded piece is injective (an immersion). -/
theorem chartRep_fderiv_injective (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) :
    Function.Injective (fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)) := by
  have hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 (G.emb a.2).e :=
    (G.emb a.2).smooth.of_le (by norm_num)
  have hli := Work.ThomBordism.PontryaginThom.frame_linearIndependent (G.emb a.2).e hf
    (G.emb a.2).injective_mfderiv (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i) hy
  rw [Fintype.linearIndependent_iff] at hli
  intro v w hvw
  set L := fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
    (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
    ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) with hL
  have hzero : L (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hdecomp : v - w = ∑ j : Fin 8, (v - w) j • EuclideanSpace.single j 1 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 8) ℝ).sum_repr (v - w)]
    exact Finset.sum_congr rfl (fun a _ => by
      rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply])
  have h1 : L (∑ j : Fin 8, (v - w) j • EuclideanSpace.single j 1)
      = ∑ j : Fin 8, (v - w) j •
          Work.ThomBordism.PontryaginThom.frame (G.emb a.2).e
            (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i) y j := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul]; rfl)
  have hsum : ∑ j : Fin 8, (v - w) j •
      Work.ThomBordism.PontryaginThom.frame (G.emb a.2).e
        (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i) y j = 0 := by
    rw [← h1, ← hdecomp, hzero]
  have hall := hli (fun j => (v - w) j) hsum
  have : v - w = 0 := by
    rw [hdecomp]
    simp only [hall, zero_smul, Finset.sum_const_zero]
  exact sub_eq_zero.mp this

/-- **The spatial derivative of the collar chart is injective.** -/
theorem spatialDeriv_injective (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) :
    Function.Injective (spatialDeriv G m a i y) := by
  have hR : 0 < G.R := tube_radius_pos (G := G) a.2
  have hv := (thetaInvAux G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) hR).2.2.1
    (xiCoord G m hpow h a y)
  rw [theta_xiCoord_eq_emb G m hpow h hspec a y] at hv
  have happ : ∀ z, (dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
      (xiCoord G m hpow h a y)) (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
        ((G.emb a.2).e y) z) = z := fun z => by
    have h := DFunLike.congr_fun hv z
    simpa using h
  have hinv : Function.Injective (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
      ((G.emb a.2).e y)) := by
    intro u w huw
    calc u = (dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
          (xiCoord G m hpow h a y)) (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
            ((G.emb a.2).e y) u) := (happ u).symm
      _ = (dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
          (xiCoord G m hpow h a y)) (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
            ((G.emb a.2).e y) w) := by rw [huw]
      _ = w := happ w
  intro u w huw
  exact chartRep_fderiv_injective G m a i y hy (hinv huw)

/-! ## §2  The level set of `vSrc` along the collar -/

/-- **`vSrc` vanishes along the collar chart**: the collar piece is a point of the level set. -/
theorem vSrc_collarPiece_eq_zero (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target)
    (hz12 : z 0 ≤ 1 / 2) :
    vSrc G m hpow (collarPiece G m hpow h a i z) = 0 := by
  set y' := (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm (tail 8 z) with hy'def
  have hy'mem : y' ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i :=
    (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.map_target hz
  have hz' : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y' :=
    ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.right_inv hz).symm
  have hcore := srcHf_collarPiece_mem_core G m hpow h hspec a i y' hy'mem z hz' hz12
  have hne' : srcHf G m hpow (collarPiece G m hpow h a i z) ≠ D.t₀ :=
    fun hh => G.t0_notMem_core (hh ▸ hcore)
  rw [vSrc, dif_neg hne']
  exact (G.core_iff_vec ⟨_, hne'⟩).mp hcore

/-- **The image of the block frame is contained in the kernel of the derivative of `vSrc`.** -/
theorem range_collarB_le_ker (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz12 : z 0 ≤ 1 / 2)
    (hBd : HasFDerivAt (collarPiece G m hpow h a i) (collarB k (spatialDeriv G m a i y)) z)
    (Lv : Work.ThomBordism.CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin (k + G.mU)))
    (hLv : HasFDerivAt (vSrc G m hpow) Lv (collarPiece G m hpow h a i z)) :
    LinearMap.range (collarB k (spatialDeriv G m a i y)).toLinearMap
      ≤ LinearMap.ker Lv.toLinearMap := by
  have hchain : HasFDerivAt (fun z' => vSrc G m hpow (collarPiece G m hpow h a i z'))
      (Lv.comp (collarB k (spatialDeriv G m a i y))) z := hLv.comp z hBd
  have hzs : (z : Work.ThomBordism.CofAtlas.E9) ∈ {z' | z' 0 ≤ 1 / 2} := hz12
  have hconv : Convex ℝ {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1 / 2} := by
    have hh : {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2}
        = {z' : Work.ThomBordism.CofAtlas.E9 | (fun w => w 0) z' ≤ (1/2 : ℝ)} := rfl
    rw [hh]
    exact convex_halfSpace_le ⟨fun x y => rfl, fun c x => rfl⟩ (1/2)
  have hIsOpen : IsOpen {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 < 1/2} :=
    isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 9 => ℝ) (0 : Fin 9)) continuous_const
  have hsub : {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 < 1/2}
      ⊆ {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2} :=
    fun z' hz' => le_of_lt (show z' 0 < 1/2 from hz')
  have hmem : (0 : Work.ThomBordism.CofAtlas.E9) ∈
      {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 < 1/2} := by norm_num
  have hint : (interior {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2}).Nonempty :=
    ⟨0, interior_maximal hsub hIsOpen hmem⟩
  have huniq : UniqueDiffWithinAt ℝ {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2} z :=
    uniqueDiffWithinAt_convex hconv hint (subset_closure hzs)
  have htarget : tail 8 z ∈ (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.target := by
    rw [hz]; exact (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.map_source hy
  have hev : (fun z' => vSrc G m hpow (collarPiece G m hpow h a i z'))
      =ᶠ[𝓝[{z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2}] z] (fun _ => 0) := by
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.open_target.preimage
      (continuous_tail 8)).mem_nhds htarget] with z' hz'tgt hz's
    exact vSrc_collarPiece_eq_zero G m hpow h hspec a i z' hz'tgt (show z' 0 ≤ 1/2 from hz's)
  have h1 : HasFDerivWithinAt (fun z' => vSrc G m hpow (collarPiece G m hpow h a i z'))
      (0 : Work.ThomBordism.CofAtlas.E9 →L[ℝ] EuclideanSpace ℝ (Fin (k + G.mU)))
      {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2} z :=
    (hev.hasFDerivWithinAt_iff
      (vSrc_collarPiece_eq_zero G m hpow h hspec a i z htarget hz12)).mpr
      (hasFDerivWithinAt_const (0 : EuclideanSpace ℝ (Fin (k + G.mU))) z _)
  have h2 : HasFDerivWithinAt (fun z' => vSrc G m hpow (collarPiece G m hpow h a i z'))
      (Lv.comp (collarB k (spatialDeriv G m a i y)))
      {z' : Work.ThomBordism.CofAtlas.E9 | z' 0 ≤ 1/2} z := hchain.hasFDerivWithinAt
  have hcomp : Lv.comp (collarB k (spatialDeriv G m a i y)) = 0 := (huniq.eq h1 h2).symm
  intro w hw
  obtain ⟨x, rfl⟩ := hw
  show Lv (collarB k (spatialDeriv G m a i y) x) = 0
  rw [← ContinuousLinearMap.comp_apply, hcomp, zero_apply]

/-! ## §3  The collar point of the collapse -/

/-- **The source homotopy at the collar piece is the collapse of the piece at the tube point.** -/
theorem srcHf_collarPiece_eq_alphaV (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz12 : z 0 ≤ 1 / 2) :
    srcHf G m hpow (collarPiece G m hpow h a i z)
      = Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
          (G.g a.2) (G.hg a.2)
          (reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) ((Fintype.equivFin ι a.2 : ℕ))
            (srcOfSpatial k (xiCoord G m hpow h a y)))) := by
  set S := familySource (D := D) (Fam := Fam) G m hpow with hS
  set j := (Fintype.equivFin ι a.2 : ℕ) with hj
  have hcp := collarPiece_eq (G := G) m hpow h a i z
  have hx0 : (collarPiece G m hpow h a i z) 0 ≤ 1 / 2 := by
    rw [hcp]
    show (srcOfSpatial k (spatialMap G m hpow h a i (tail 8 z))).ofLp 0
      + ((z 0) • (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0 ≤ 1 / 2
    rw [srcOfSpatial_zero, zero_add, PiLp.smul_apply, smul_eq_mul, eZero_apply, mul_one]
    exact hz12
  have htail : Work.PTGeometric.tail (k + 8) (srcCast k (collarPiece G m hpow h a i z))
      = xiCoord G m hpow h a y := by
    rw [hcp, tail_srcCast_srcOfSpatial_add]
    show xiCoord G m hpow h a ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm
      (tail 8 z)) = xiCoord G m hpow h a y
    rw [hz, (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.left_inv hy]
  have hval : srcHf G m hpow (collarPiece G m hpow h a i z)
      = alphaFamily (D := D) (Fam := Fam) G m
          (collPt k (srcOfSpatial k (xiCoord G m hpow h a y))) := by
    rw [srcHf, flatSourceHomotopy8_eq_collapse (k := k) S.H S.φ
      (alphaFamily (D := D) (Fam := Fam) G m) S.collar hx0]
    exact congrArg (alphaFamily (D := D) (Fam := Fam) G m) (by rw [← htail]; rfl)
  rw [hval]
  set v := xiCoord G m hpow h a y with hv
  have hb := blockStrict G m hpow h hspec a y
  have hcollv : collPt k (srcOfSpatial k v) = cubeCoord (k + 8) v := by
    rw [collPt, tail_srcCast_srcOfSpatial]
  have hIlo : 1 < (2 : ℝ) ^ ((a.1 : ℕ) + 1) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollv]; exact hb.1
  have hIhi : (2 : ℝ) ^ ((a.1 : ℕ)) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollv]; exact hb.2.1
  have hJlo : 1 < (2 : ℝ) ^ (j + 1) *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollv]; exact hb.2.2.1
  have hJhi : (2 : ℝ) ^ j *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollv]; exact hb.2.2.2
  have hgeom : (G.rep a.2).collapse (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))
      = Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
          (G.g a.2) (G.hg a.2)
          (reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))) := by
    have hh := G.isGeom a.2 (reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j
      (srcOfSpatial k v)))
    rwa [reIdx_comp_finKR k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))] at hh
  rw [← hgeom]
  have hpiece : (G.rep a.2).collapse (clipPt k (cZero k) (cOne k) (a.1 : ℕ) j (srcOfSpatial k v))
      = alphaFamily (D := D) (Fam := Fam) G m (collPt k (srcOfSpatial k v)) := by
    have hh := alphaFamily_eq_collapse_of_block (G := G) m (a.1 : ℕ) j (a.1).2
      (Fintype.equivFin ι a.2).2 (srcOfSpatial k v) hIlo hIhi hJlo hJhi
    have hiχ : (Fintype.equivFin ι).symm ⟨j, (Fintype.equivFin ι a.2).2⟩ = a.2 :=
      Equiv.symm_apply_apply (Fintype.equivFin ι) a.2
    rw [hiχ] at hh
    exact hh.symm
  rw [hpiece]

/-- **The tube point of the collar piece is the embedded piece point.** -/
theorem cubeToEuc_clipPt_collarPiece (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt) :
    Work.Tubular.cubeToEuc (8 + k) G.R
      (reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) ((Fintype.equivFin ι a.2 : ℕ))
        (srcOfSpatial k (xiCoord G m hpow h a y)))) = (G.emb a.2).e y := by
  set j := (Fintype.equivFin ι a.2 : ℕ) with hj
  set v := xiCoord G m hpow h a y with hv
  have hb := blockStrict G m hpow h hspec a y
  have hcollv : collPt k (srcOfSpatial k v) = cubeCoord (k + 8) v := by
    rw [collPt, tail_srcCast_srcOfSpatial]
  have hIlo : 1 < (2 : ℝ) ^ ((a.1 : ℕ) + 1) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollv]; exact hb.1
  have hIhi : (2 : ℝ) ^ ((a.1 : ℕ)) *
      ((collPt k (srcOfSpatial k v) (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollv]; exact hb.2.1
  have hJlo : 1 < (2 : ℝ) ^ (j + 1) *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [hcollv]; exact hb.2.2.1
  have hJhi : (2 : ℝ) ^ j *
      ((collPt k (srcOfSpatial k v) (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [hcollv]; exact hb.2.2.2
  rw [← modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) (a.1 : ℕ) j (srcOfSpatial k v)
    hIlo hIhi hJlo hJhi]
  exact theta_xiCoord_eq_emb G m hpow h hspec a y


/-- The spatial coordinates of a collar piece. -/
theorem tail_srcCast_collarPiece (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :
    Work.PTGeometric.tail (k + 8) (srcCast k (collarPiece G m hpow h a i z))
      = xiCoord G m hpow h a y := by
  have hcp := collarPiece_eq (G := G) m hpow h a i z
  rw [hcp, tail_srcCast_srcOfSpatial_add]
  show xiCoord G m hpow h a ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm
    (tail 8 z)) = xiCoord G m hpow h a y
  rw [hz, (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.left_inv hy]

/-- **The projection field of the ambient coordinates at a collar point** is the padded tube
projection at the piece point. -/
theorem coord_collarPiece_fst (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz12 : z 0 ≤ 1 / 2)
    (hne : srcHf G m hpow (collarPiece G m hpow h a i z) ≠ D.t₀) :
    (G.coord ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩).1
      = padEndEuc k G.mU G.hmU
          (tubeNormalProj (G.emb a.2) (G.chart a.2) ((G.emb a.2).e y)) := by
  set t := reIdx k (clipPt k (cZero k) (cOne k) (a.1 : ℕ) ((Fintype.equivFin ι a.2 : ℕ))
      (srcOfSpatial k (xiCoord G m hpow h a y))) with ht
  have hsrcHf := srcHf_collarPiece_eq_alphaV G m hpow h hspec a i y hy z hz hz12
  have hcube := cubeToEuc_clipPt_collarPiece G m hpow h hspec a i y
  have htube : Work.Tubular.cubeToEuc (8 + k) G.R t ∈ (G.chart a.2).openTube := by
    rw [hcube]; exact (G.chart a.2).mem_openTube y
  obtain ⟨hne', hcoord⟩ := G.coord_collapse a.2 t htube
  have hpt : (⟨Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2) (G.hJ a.2)
      (G.g a.2) (G.hg a.2) t, hne'⟩ : {x : D.T // x ≠ D.t₀})
      = ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩ := Subtype.ext hsrcHf.symm
  rw [← hpt]
  have hfst : (G.coord ⟨Work.Tubular.alphaV (G.chart a.2) G.hR (G.hbox a.2) D.t₀ (G.J a.2)
      (G.hJ a.2) (G.g a.2) (G.hg a.2) t, hne'⟩).1 = padEndEuc k G.mU G.hmU
        (tubeNormalProj (G.emb a.2) (G.chart a.2) (Work.Tubular.cubeToEuc (8 + k) G.R t)) :=
    congrArg Prod.fst hcoord
  rw [hfst, hcube]

/-! ## §4  The model: `vSrc` is the padded tube normal coordinate -/

/-- The cube coordinates of a spatial point are unchanged by the collar coordinate. -/
theorem collPt_srcOfSpatial_tail (k : ℕ) (u : Work.ThomBordism.CofAtlas.ModN k) :
    collPt k (srcOfSpatial k (Work.PTGeometric.tail (k + 8) (srcCast k u))) = collPt k u := by
  rw [collPt, collPt, tail_srcCast_srcOfSpatial]

/-- **The block model depends on the ambient point only through its spatial coordinates.** -/
theorem modelEuc_eq_theta_tail (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (a : Fin m × ι) (u : Work.ThomBordism.CofAtlas.ModN k) :
    modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u
      = theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
          (Work.PTGeometric.tail (k + 8) (srcCast k u)) := by
  have h1 : collPt k (srcOfSpatial k (Work.PTGeometric.tail (k + 8) (srcCast k u))) = collPt k u :=
    collPt_srcOfSpatial_tail k u
  show eucOfReal (8 + k) G.R
      (fun l => modelPoint k (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u
        (finKRInv k l))
    = eucOfReal (8 + k) G.R
      (fun l => modelPoint k (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
        (srcOfSpatial k (Work.PTGeometric.tail (k + 8) (srcCast k u))) (finKRInv k l))
  congr 1

/-- **The model is differentiable at a collar point**, with the derivative of `theta` on the spatial
coordinates. -/
theorem hasFDerivAt_modelEuc (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :
    HasFDerivAt (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
      ((dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y)).comp
        ((tailCLM (k + 8)).comp (srcCast k)))
      (collarPiece G m hpow h a i z) := by
  have htail := tail_srcCast_collarPiece G m hpow h hspec a i y hy z hz
  have h1 : HasFDerivAt ((tailCLM (k + 8)).comp (srcCast k))
      ((tailCLM (k + 8)).comp (srcCast k)) (collarPiece G m hpow h a i z) :=
    ((tailCLM (k + 8)).comp (srcCast k)).hasFDerivAt
  have h2 : HasFDerivAt (theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
      (dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
        (Work.PTGeometric.tail (k + 8) (srcCast k (collarPiece G m hpow h a i z))))
      (Work.PTGeometric.tail (k + 8) (srcCast k (collarPiece G m hpow h a i z))) :=
    ((differentiableAt_theta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) _)).hasFDerivAt
  have h3 := h2.comp (collarPiece G m hpow h a i z) h1
  rw [htail] at h3
  exact h3.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => modelEuc_eq_theta_tail G m a u))

/-- **The derivative of the block model composed with the spatial embedding is the derivative of the
block model `theta`.** -/
theorem fderiv_modelEuc_comp_srcOfSpatialCLM (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :
    (fderiv ℝ (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
        (collarPiece G m hpow h a i z)).comp (srcOfSpatialCLM k)
      = dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y) := by
  rw [(hasFDerivAt_modelEuc G m hpow h hspec a i y hy z hz).fderiv]
  refine ContinuousLinearMap.ext (fun w => ?_)
  simp only [ContinuousLinearMap.comp_apply]
  rw [show (tailCLM (k + 8)) (srcCast k (srcOfSpatialCLM k w)) = w from by
    rw [srcOfSpatialCLM_apply]
    exact tail_srcCast_srcOfSpatial k w]

/-! ## §5  The rank of the Gauss frame -/

/-- The orthogonal frame map of an oriented plane is injective. -/
theorem ogFrameCLM_injective {m : ℕ} (Γ : Work.ThomBordism.Grassmann.OG k m) :
    Function.Injective (ogFrameCLM Γ) := by
  have horth : ∀ a b, inner ℝ ((Quotient.out Γ).1 a) ((Quotient.out Γ).1 b)
      = if a = b then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp (Quotient.out Γ).2
  have hval : ∀ x : EuclideanSpace ℝ (Fin k),
      ogFrameCLM Γ x = ∑ a : Fin k, x a • (Quotient.out Γ).1 a := by
    intro x
    rw [ogFrameCLM, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun a _ => by
      rw [ContinuousLinearMap.smulRight_apply, PiLp.proj_apply])
  intro x y hxy
  have hzero : ogFrameCLM Γ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hfun0 : ∀ b, (x - y) b = 0 := by
    intro b
    have hkey : inner ℝ ((Quotient.out Γ).1 b) (ogFrameCLM Γ (x - y)) = (x - y) b := by
      rw [hval (x - y), inner_sum, Finset.sum_eq_single b]
      · rw [inner_smul_right, horth b b, if_pos rfl, mul_one]
      · intro a _ hab
        rw [inner_smul_right, horth b a, if_neg (Ne.symm hab), mul_zero]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    rw [hzero, inner_zero_right] at hkey
    exact hkey.symm
  have h0 : x - y = 0 := by
    ext b
    simpa using hfun0 b
  exact sub_eq_zero.mp h0

/-- **The Gauss frame spans a `k`-dimensional space.** -/
theorem finrank_range_ogFrameCLM {m : ℕ} (Γ : Work.ThomBordism.Grassmann.OG k m) :
    Module.finrank ℝ ↥(LinearMap.range (ogFrameCLM Γ).toLinearMap) = k := by
  exact (LinearMap.finrank_range_of_inj (ogFrameCLM_injective Γ)).trans
    finrank_euclideanSpace_fin


/-- The model point of the collar point is the embedded piece point. -/
theorem modelEuc_collarPiece_eq_emb (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :
    modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
        (collarPiece G m hpow h a i z) = (G.emb a.2).e y := by
  rw [modelEuc_eq_theta_tail G m a,
    tail_srcCast_collarPiece G m hpow h hspec a i y hy z hz]
  exact theta_xiCoord_eq_emb G m hpow h hspec a y

/-- **The derivative of the padded tube normal coordinate of the block model at a collar point.** -/
theorem fderiv_padEuc_tubeNormalCoord_model (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y) :
    fderiv ℝ (fun u : Work.ThomBordism.CofAtlas.ModN k => padEuc k G.mU G.hmU
        (tubeNormalCoord (G.emb a.2) (G.chart a.2)
          (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)))
      (collarPiece G m hpow h a i z)
    = (padEuc k G.mU G.hmU).comp
        ((fderiv ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y)).comp
          (fderiv ℝ (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
            (collarPiece G m hpow h a i z))) := by
  have hpt : modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
      (collarPiece G m hpow h a i z) = (G.emb a.2).e y :=
    modelEuc_collarPiece_eq_emb G m hpow h hspec a i y hy z hz
  have hNCdiff : DifferentiableAt ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2))
      ((G.emb a.2).e y) := by
    have hh : ContDiffAt ℝ ∞ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y) :=
      ((contMDiffOn_tubeNormalCoord (G.emb a.2) (G.chart a.2)).contMDiffAt
        ((G.chart a.2).openTube_isOpen.mem_nhds ((G.chart a.2).mem_openTube y))).contDiffAt
    exact hh.differentiableAt (by simp)
  have hAffdiff : DifferentiableAt ℝ
      (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
      (collarPiece G m hpow h a i z) :=
    (((contMDiff_modelEuc G (cZero k) (cOne k) (a.1 : ℕ)
      (Fintype.equivFin ι a.2 : ℕ)).contMDiffAt).contDiffAt).differentiableAt (by simp)
  have hNC : HasFDerivAt (tubeNormalCoord (G.emb a.2) (G.chart a.2))
      (fderiv ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y))
      ((G.emb a.2).e y) := hNCdiff.hasFDerivAt
  have hNC' : HasFDerivAt (tubeNormalCoord (G.emb a.2) (G.chart a.2))
      (fderiv ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y))
      (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
        (collarPiece G m hpow h a i z)) := by
    rw [hpt]
    exact hNC
  have h1 := hNC'.comp (collarPiece G m hpow h a i z) hAffdiff.hasFDerivAt
  have h2 := (padEuc k G.mU G.hmU).hasFDerivAt.comp
    (collarPiece G m hpow h a i z) h1
  show fderiv ℝ (fun u : Work.ThomBordism.CofAtlas.ModN k => padEuc k G.mU G.hmU
      (tubeNormalCoord (G.emb a.2) (G.chart a.2)
        (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u)))
      (collarPiece G m hpow h a i z)
    = (padEuc k G.mU G.hmU).comp
        ((fderiv ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y)).comp
          (fderiv ℝ (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
            (collarPiece G m hpow h a i z)))
  exact h2.fderiv

/-- **The value of `Lv` on the canonical normal frame is the Gauss frame.** -/
theorem Lv_frameN (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (hspec : BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i) (z : Work.ThomBordism.CofAtlas.E9)
    (hz : tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz12 : z 0 ≤ 1 / 2)
    (hne : srcHf G m hpow (collarPiece G m hpow h a i z) ≠ D.t₀)
    (hmodel : (fun u : Work.ThomBordism.CofAtlas.ModN k => vSrc G m hpow u)
      =ᶠ[𝓝 (collarPiece G m hpow h a i z)]
      (fun u => padEuc k G.mU G.hmU
        (tubeNormalCoord (G.emb a.2) (G.chart a.2)
          (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) u))))
    (Lv : Work.ThomBordism.CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin (k + G.mU)))
    (hLv : HasFDerivAt (vSrc G m hpow) Lv (collarPiece G m hpow h a i z))
    (v : EuclideanSpace ℝ (Fin k)) :
    Lv (frameN G m hpow h a i y z hne v)
      = ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v := by
  have hR : 0 < G.R := tube_radius_pos (G := G) a.2
  -- the derivative identity
  have hLveq : Lv = (padEuc k G.mU G.hmU).comp
      ((fderiv ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y)).comp
        (fderiv ℝ (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
          (collarPiece G m hpow h a i z))) := by
    rw [← hLv.fderiv, hmodel.fderiv_eq]
    exact fderiv_padEuc_tubeNormalCoord_model G m hpow h hspec a i y hy z hz
  -- the derivative of the normal coordinate is the tube projection
  have hP : fderiv ℝ (tubeNormalCoord (G.emb a.2) (G.chart a.2)) ((G.emb a.2).e y)
      = tubeNormalProj (G.emb a.2) (G.chart a.2) ((G.emb a.2).e y) :=
    fderiv_normalCoord_eq_tubeNormalProj (G.emb a.2) (G.chart a.2) y
  -- the model derivative composed with the spatial embedding is `dtheta`
  have hkey : ∀ u : EuclideanSpace ℝ (Fin (k + 8)),
      (fderiv ℝ (modelEuc G (cZero k) (cOne k) (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ))
        (collarPiece G m hpow h a i z)) (srcOfSpatialCLM k u)
        = dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y) u :=
    fun u => by
      have hh := congrArg (fun (L : EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ]
          EuclideanSpace ℝ (Fin (8 + k))) => L u)
        (fderiv_modelEuc_comp_srcOfSpatialCLM G m hpow h hspec a i y hy z hz)
      simpa using hh
  -- `dtheta v ∘ dthetaInv y₀ = 1`
  have htheta : ∀ w : EuclideanSpace ℝ (Fin (8 + k)),
      dtheta G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) (xiCoord G m hpow h a y)
        (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y) w) = w := by
    have hv' := (thetaInvAux G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) hR).2.2.1
      (xiCoord G m hpow h a y)
    rw [theta_xiCoord_eq_emb G m hpow h hspec a y] at hv'
    intro w
    have hh := DFunLike.congr_fun hv' w
    simpa using hh
  -- the coordinate identification
  have hcoord := coord_collarPiece_fst G m hpow h hspec a i y hy z hz hz12 hne
  -- the Gauss frame is fixed by the projection field
  have hWmem : ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v
      ∈ Set.range (ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩)) :=
    ⟨v, rfl⟩
  rw [range_ogFrameCLM_gauss] at hWmem
  have hPfix : tubeNormalProj (G.emb a.2) (G.chart a.2) ((G.emb a.2).e y)
      (projEuc k G.mU G.hmU (ogFrameCLM
        (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v))
      = projEuc k G.mU G.hmU (ogFrameCLM
        (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v) := by
    have hh := hWmem
    rw [hcoord] at hh
    simp only [Set.mem_setOf_eq] at hh
    rw [padEndEuc_apply] at hh
    have := congrArg (projEuc k G.mU G.hmU) hh
    rwa [projEuc_padEuc] at this
  have hWpad : padEuc k G.mU G.hmU (projEuc k G.mU G.hmU (ogFrameCLM
      (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v))
      = ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v := by
    have hh := hWmem
    rw [hcoord] at hh
    simp only [Set.mem_setOf_eq] at hh
    rw [padEndEuc_apply] at hh
    rw [hPfix] at hh
    exact hh
  have hframe : frameN G m hpow h a i y z hne v
      = srcOfSpatialCLM k (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ)
          ((G.emb a.2).e y) (projEuc k G.mU G.hmU (ogFrameCLM
            (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v))) := rfl
  rw [hLveq, hframe]
  simp only [ContinuousLinearMap.comp_apply]
  simp only [hkey, htheta, hP]
  rw [hPfix]
  exact hWpad

theorem tubeDetKernel {k : ℕ} (hk : 1 ≤ k)
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (h : Work.ThomBordism.LeadChapter.BdryId G m hpow)
    (hspec : Work.ThomBordism.LeadChapter.BdryIdSpec G m hpow h) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (hy : y ∈ Work.ThomBordism.FrameSigns.src (Fam a.2) i)
    (z : Work.ThomBordism.CofAtlas.E9)
    (hz : Work.PTGeometric.tail 8 z = (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y)
    (hz0 : 0 < z 0) (hz12 : z 0 ≤ 1 / 2)
    (hne : Work.ThomBordism.LeadChapter.srcHf G m hpow
      (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z) ≠ D.t₀)
    (hBd : HasFDerivAt (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i)
      (Work.ThomBordism.LeadChapter.collarB k
        (Work.ThomBordism.LeadChapter.spatialDeriv G m a i y)) z)
    (Lv : Work.ThomBordism.CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin (k + G.mU)))
    (hLv : HasFDerivAt (Work.ThomBordism.LeadChapter.vSrc G m hpow) Lv
      (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z)) :
    LinearMap.ker Lv.toLinearMap
        = LinearMap.range (Work.ThomBordism.LeadChapter.collarB k
            (Work.ThomBordism.LeadChapter.spatialDeriv G m a i y)).toLinearMap ∧
      (∀ N : EuclideanSpace ℝ (Fin k) →L[ℝ] Work.ThomBordism.CofAtlas.ModN k,
        Lv.comp N = Work.ThomBordism.LeadChapter.ogFrameCLM
            (G.gauss ⟨Work.ThomBordism.LeadChapter.srcHf G m hpow
              (Work.ThomBordism.LeadChapter.collarPiece G m hpow h a i z), hne⟩) →
        ∀ v, N v - Work.ThomBordism.LeadChapter.frameN G m hpow h a i y z hne v ∈
          LinearMap.range (Work.ThomBordism.LeadChapter.collarB k
            (Work.ThomBordism.LeadChapter.spatialDeriv G m a i y)).toLinearMap) := by
  have hmodel := vSrcEventualModel G m hpow h hspec a i y hy z hz hz12 hne
  have hframe := Lv_frameN G m hpow h hspec a i y hy z hz hz12 hne hmodel Lv hLv
  have hle := range_collarB_le_ker G m hpow h hspec a i y hy z hz hz12 hBd Lv hLv
  have hAinj : Function.Injective (spatialDeriv G m a i y) :=
    spatialDeriv_injective G m hpow h hspec a i y hy
  have hfinB : Module.finrank ℝ
      ↥(LinearMap.range (collarB k (spatialDeriv G m a i y)).toLinearMap) = 9 := by
    rw [LinearMap.finrank_range_of_inj (collarB_injective (spatialDeriv G m a i y) hAinj)]
    exact finrank_euclideanSpace_fin
  have hmono : LinearMap.range (ogFrameCLM
        (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩)).toLinearMap
      ≤ Lv.toLinearMap.range := by
    rintro w ⟨v, rfl⟩
    exact ⟨frameN G m hpow h a i y z hne v, hframe v⟩
  have hk_le : k ≤ Module.finrank ℝ ↥(Lv.toLinearMap.range) := by
    have hh := Submodule.finrank_mono hmono
    rwa [finrank_range_ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z),
      hne⟩)] at hh
  have hker_le : Module.finrank ℝ ↥(Lv.toLinearMap.ker) ≤ 9 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker Lv.toLinearMap
    have hdim : Module.finrank ℝ (Work.ThomBordism.CofAtlas.ModN k) = (8 + k) + 1 :=
      finrank_euclideanSpace_fin
    omega
  have hfin_ker : Module.finrank ℝ ↥(Lv.toLinearMap.ker) = 9 :=
    le_antisymm hker_le (by rw [← hfinB]; exact Submodule.finrank_mono hle)
  have hker : Lv.toLinearMap.ker
      = LinearMap.range (collarB k (spatialDeriv G m a i y)).toLinearMap :=
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin_ker, hfinB])).symm
  refine ⟨hker, ?_⟩
  intro N hN v
  have h1 : Lv (N v)
      = ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩) v :=
    DFunLike.congr_fun hN v
  have h0 : Lv (N v - frameN G m hpow h a i y z hne v) = 0 := by
    rw [map_sub, h1, hframe v, sub_self]
  have hmem : N v - frameN G m hpow h a i y z hne v ∈ Lv.toLinearMap.ker :=
    LinearMap.mem_ker.mpr h0
  rwa [hker] at hmem

end

end Work.ThomBordism.LeadChapter
