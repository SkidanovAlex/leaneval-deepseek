import Mathlib
import Submission.Work.Agree.Basic
import Submission.Work.Glue.mdifferentiable_iota_smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The restriction of the tangent bundle of `X = D(ξ) ∪_F D⁸` to the disc-bundle piece

For a capping datum `D` (so that `X = D.Glued` is the closed `8`-manifold `D(ξ) ∪_F D⁸`), the
pullback of the tangent bundle of `X` along the open embedding `D.ιX : D(ξ) = Vk (-2) → X` is
isomorphic to the tangent bundle of the open piece `D(ξ)`.

The isomorphism is not the identity on the fibres in the *chart* conventions of the two bundles:
the two bundles carry tangent vectors of two different manifolds, and the identification is the
differential of the open embedding `D.ιX` (equivalently, of its inverse `D.homX.symm`).  We build
the isomorphism with

* `hom b = mfderiv (⇑D.homX.symm) (D.ιX b)`, the derivative of the inverse local diffeomorphism,
* `inv b = mfderiv (⇑D.ιX) b`,

and prove the continuity of the two total-space maps by exhibiting them as composites of the
continuity of the pullback map (`Work.Thom.continuous_totalSpaceMap`) with the continuity of the
bundled derivatives `tangentMap`/`tangentMapWithin` (`ContMDiff.continuous_tangentMap`,
`ContMDiffOn.continuousOn_tangentMapWithin`); the smoothness of `D.homX` and of `D.homX.symm` is
`Work.Glue.liftProp_homX_gen`.
-/

namespace Work.Agree

open scoped Manifold ContDiff Topology
open Bundle

noncomputable section

/-- A capping datum, spelled out (reducibly, so that its fields are available definitionally). -/
abbrev CapDatum : Type _ :=
  Submission.Glue.Data Work.Milnor.mMSpace8 ∞ (Submission.Milnor.Vk (-2))
    (EuclideanSpace ℝ (Fin 8))

/-- The open embedding `D(ξ) = Vk (-2) → X = D.Glued` of a capping datum, as a continuous map. -/
abbrev inclOf (D : CapDatum) : C(Submission.Milnor.Vk (-2), D.Glued) :=
  ⟨D.ιX, D.continuous_ιX⟩

/-- The pullback of the tangent bundle of `X = D.Glued` along the inclusion of the disc bundle. -/
abbrev TBpull (D : CapDatum) : VectorBundleCore ℝ (Submission.Milnor.Vk (-2))
    Submission.Milnor.MSpace8 (atlas Submission.Milnor.MSpace8 D.Glued) :=
  Work.Thom.bundleComap
    (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 D.Glued) (inclOf D)

/-- The tangent bundle of the disc bundle `D(ξ) = Vk (-2)`. -/
abbrev TBdisc : VectorBundleCore ℝ (Submission.Milnor.Vk (-2)) Submission.Milnor.MSpace8
    (atlas Submission.Milnor.MSpace8 (Submission.Milnor.Vk (-2))) :=
  Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 (Submission.Milnor.Vk (-2))

/-- The derivative of the inverse of the open embedding, as a fibrewise linear map. -/
abbrev homLM (D : CapDatum) (b : Submission.Milnor.Vk (-2)) :
    Submission.Milnor.MSpace8 →ₗ[ℝ] Submission.Milnor.MSpace8 :=
  (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) (D.ιX b)).toLinearMap

/-- The derivative of the open embedding, as a fibrewise linear map. -/
abbrev invLM (D : CapDatum) (b : Submission.Milnor.Vk (-2)) :
    Submission.Milnor.MSpace8 →ₗ[ℝ] Submission.Milnor.MSpace8 :=
  (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX b).toLinearMap

/-! ## The topology of a pullback bundle

A map into the total space of `bundleComap Z f` is continuous as soon as its projection to the base
and its composition with the pullback map `⟨b, v⟩ ↦ ⟨f b, v⟩` are: the topology of
`(bundleComap Z f).TotalSpace` is the initial topology of the two. -/
theorem continuous_comap_of_components {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : VectorBundleCore ℝ B F ι) (f : C(B', B)) {Y : Type*} [TopologicalSpace Y]
    (g : Y → (Work.Thom.bundleComap Z f).TotalSpace)
    (h₁ : Continuous fun y => (g y).1)
    (h₂ : Continuous fun y => (⟨f (g y).1, (g y).2⟩ : Z.TotalSpace)) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro y₀
  set i : ι := (Work.Thom.bundleComap Z f).indexAt (g y₀).1 with hi
  set V : Set Y := {y : Y | (g y).1 ∈ (Work.Thom.bundleComap Z f).baseSet i} with hV
  have hVopen : IsOpen V := h₁.isOpen_preimage _ ((Work.Thom.bundleComap Z f).isOpen_baseSet i)
  have hy₀V : y₀ ∈ V := (Work.Thom.bundleComap Z f).mem_baseSet_at (g y₀).1
  have hbV : ∀ y ∈ V, f (g y).1 ∈ Z.baseSet i := by
    intro y hy
    have hy' : (g y).1 ∈ (Work.Thom.bundleComap Z f).baseSet i := hy
    rwa [Work.Thom.bundleComap_baseSet] at hy'
  have hsndeq : ∀ y : Y, ((Work.Thom.bundleComap Z f).localTriv i (g y)).2 =
      ((Z.localTriv i) (⟨f (g y).1, (g y).2⟩ : Z.TotalSpace)).2 := by
    intro y
    rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
    rfl
  have hT : ContinuousOn
      (fun y : Y => (Work.Thom.bundleComap Z f).localTriv i (g y)) V := by
    refine ContinuousOn.prodMk h₁.continuousOn ?_
    have hZc : ContinuousOn
        (fun y : Y => (Z.localTriv i) (⟨f (g y).1, (g y).2⟩ : Z.TotalSpace)) V :=
      (Z.localTriv i).continuousOn.comp h₂.continuousOn (fun y hy => by
        rw [VectorBundleCore.mem_localTriv_source]
        exact hbV y hy)
    refine (continuous_snd.comp_continuousOn hZc).congr ?_
    intro y hy
    exact hsndeq y
  have hsymm : ContinuousOn
      (fun q : B' × F => ((Work.Thom.bundleComap Z f).localTriv i).toOpenPartialHomeomorph.symm q)
      ((Work.Thom.bundleComap Z f).localTriv i).target :=
    ((Work.Thom.bundleComap Z f).localTriv i).toOpenPartialHomeomorph.continuousOn_symm
  have hmap : Set.MapsTo (fun y : Y => (Work.Thom.bundleComap Z f).localTriv i (g y)) V
      ((Work.Thom.bundleComap Z f).localTriv i).target := by
    intro y hy
    rw [VectorBundleCore.mem_localTriv_target]
    exact hy
  have hcontV : ContinuousOn g V := by
    refine (hsymm.comp hT hmap).congr ?_
    intro y hy
    exact (((Work.Thom.bundleComap Z f).localTriv i).toOpenPartialHomeomorph.left_inv
      (by
        rw [VectorBundleCore.mem_localTriv_source]
        exact hy)).symm
  exact hcontV.continuousAt (hVopen.mem_nhds hy₀V)

/-! ## The smoothness of the capping datum -/

/-- `D.homX` and `D.homX.symm` are smooth. -/
theorem contMDiff_homX (D : CapDatum) :
    ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 ∞ (⇑D.homX) D.homX.source ∧
    ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 ∞ (⇑D.homX.symm) D.homX.target := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  exact (isLocalStructomorphOn_contDiffGroupoid_iff
    (I := Work.Milnor.mMSpace8) (n := ∞) (f := D.homX)).mp (Work.Glue.liftProp_homX_gen D)

/-- The tangent map of the inclusion is continuous. -/
theorem continuous_tangentMap_iota (D : CapDatum) :
    Continuous (tangentMap Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX) := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  have hCD1 := (contMDiff_homX D).1
  have h : ContMDiff Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 ∞ (⇑D.homX) := by
    rw [D.homX_source, contMDiffOn_univ] at hCD1
    exact hCD1
  have h2 := h.continuous_tangentMap (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  rwa [Work.Glue.homX_coe D] at h2

/-- The tangent map of the inverse of the inclusion is continuous, on the piece where it is
defined. -/
theorem continuousOn_tangentMap_symm (D : CapDatum) :
    ContinuousOn (tangentMapWithin Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm)
      D.homX.target) (Bundle.TotalSpace.proj ⁻¹' D.homX.target) := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  exact (contMDiff_homX D).2.continuousOn_tangentMapWithin (by norm_num : (1 : ℕ∞ω) ≤ ∞)
    D.homX.open_target.uniqueMDiffOn

/-- The two chain rules: the derivatives of `D.ιX` and of `D.homX.symm` are mutually inverse. -/
theorem mfderiv_iota_symm (D : CapDatum) :
    (∀ (b : Submission.Milnor.Vk (-2)) (v : Submission.Milnor.MSpace8),
        mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX b
          (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) (D.ιX b) v) = v) ∧
    (∀ (b : Submission.Milnor.Vk (-2)) (w : Submission.Milnor.MSpace8),
        mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) (D.ιX b)
          (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX b w) = w) := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  obtain ⟨hCD1, hCD2⟩ := contMDiff_homX D
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hxt : ∀ b : Submission.Milnor.Vk (-2), D.ιX b ∈ D.homX.target := by
    intro b
    rw [D.homX_target]; exact ⟨b, rfl⟩
  have hMDsymm : ∀ b : Submission.Milnor.Vk (-2),
      MDifferentiableAt Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) (D.ιX b) :=
    fun b => ((hCD2.mdifferentiableOn hn) _ (hxt b)).mdifferentiableAt
      (D.homX.open_target.mem_nhds (hxt b))
  have hMDincl : ∀ b : Submission.Milnor.Vk (-2),
      MDifferentiableAt Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX b := by
    intro b
    have h := ((hCD1.mdifferentiableOn hn) b (Set.mem_univ b)).mdifferentiableAt Filter.univ_mem
    rwa [Work.Glue.homX_coe D] at h
  constructor
  · intro b v
    have hMDincl' : MDifferentiableAt Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX
        (⇑D.homX.symm (D.ιX b)) := by
      rw [D.homX_symm_apply b]; exact hMDincl b
    have key := mfderiv_comp (I := Work.Milnor.mMSpace8) (I' := Work.Milnor.mMSpace8)
      (I'' := Work.Milnor.mMSpace8) (x := D.ιX b) (f := ⇑D.homX.symm) (g := D.ιX)
      hMDincl' (hMDsymm b)
    have hev : (D.ιX ∘ ⇑D.homX.symm) =ᶠ[𝓝 (D.ιX b)] id := by
      filter_upwards [D.homX.open_target.mem_nhds (hxt b)] with z hz
      obtain ⟨y, rfl⟩ := D.homX_target ▸ hz
      exact congrArg D.ιX (D.homX_symm_apply y)
    have hL : mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (D.ιX ∘ ⇑D.homX.symm)
        (D.ιX b) = ContinuousLinearMap.id ℝ Submission.Milnor.MSpace8 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id]
      rfl
    have hcomp : ((mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX
          (⇑D.homX.symm (D.ιX b))).comp
        (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) (D.ιX b))) =
        ContinuousLinearMap.id ℝ Submission.Milnor.MSpace8 := by
      rw [← key, hL]
    have h := congrArg
      (fun (L : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8) => L v) hcomp
    simp only [ContinuousLinearMap.id_apply] at h
    rw [mfderiv_congr_point (I := Work.Milnor.mMSpace8) (I' := Work.Milnor.mMSpace8)
      (f := D.ιX) (D.homX_symm_apply b)] at h
    exact h
  · intro b w
    have key := mfderiv_comp (I := Work.Milnor.mMSpace8) (I' := Work.Milnor.mMSpace8)
      (I'' := Work.Milnor.mMSpace8) (x := b) (f := D.ιX) (g := ⇑D.homX.symm)
      (hMDsymm b) (hMDincl b)
    have hid : (⇑D.homX.symm ∘ D.ιX) = id := funext (fun y => D.homX_symm_apply y)
    have hL : mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm ∘ D.ιX) b =
        ContinuousLinearMap.id ℝ Submission.Milnor.MSpace8 := by
      rw [mfderiv_congr (I := Work.Milnor.mMSpace8) (I' := Work.Milnor.mMSpace8) (x := b) hid,
        mfderiv_id]
      rfl
    have hcomp : ((mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm)
          (D.ιX b)).comp
        (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX b)) =
        ContinuousLinearMap.id ℝ Submission.Milnor.MSpace8 := by
      rw [← key, hL]
    have h := congrArg
      (fun (L : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8) => L w) hcomp
    simp only [ContinuousLinearMap.id_apply] at h
    exact h

/-- The total-space map `⟨b, v⟩ ↦ ⟨b, homLM D b v⟩` of the restriction isomorphism. -/
theorem continuous_homLM (D : CapDatum) : Continuous (fun p : (TBpull D).TotalSpace =>
    (tangentMapWithin Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) D.homX.target
      (⟨D.ιX p.1, p.2⟩ : (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
        D.Glued).TotalSpace))) := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  have hpb : Continuous (fun p : (TBpull D).TotalSpace =>
      (⟨D.ιX p.1, p.2⟩ : (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
        D.Glued).TotalSpace)) :=
    Work.Thom.continuous_totalSpaceMap _ _ (inclOf D) (fun i => rfl) (fun x i => rfl)
  exact (continuousOn_tangentMap_symm D).comp_continuous hpb (fun p => by
    show D.ιX p.1 ∈ D.homX.target
    rw [D.homX_target]; exact ⟨p.1, rfl⟩)

/-- The total-space map `⟨b, v⟩ ↦ ⟨b, invLM D b v⟩` of the restriction isomorphism. -/
theorem continuous_invLM (D : CapDatum) : Continuous (fun q : (TBdisc).TotalSpace =>
    (⟨q.1, (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX q.1).toLinearMap q.2⟩ :
      (TBpull D).TotalSpace)) := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  refine continuous_comap_of_components
    (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 D.Glued) (inclOf D) _ ?_ ?_
  · exact TBdisc.continuous_proj
  · refine (continuous_tangentMap_iota D).congr (fun q => ?_)
    change tangentMap Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX q =
      (⟨D.ιX q.1, (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 D.ιX q.1).toLinearMap q.2⟩ :
        (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 D.Glued).TotalSpace)
    rfl

/-- **The restriction of the tangent bundle of `X = D(ξ) ∪_F D⁸` to the disc bundle.** -/
theorem tangentRestriction_datum (D : CapDatum) :
    Nonempty (Work.Thom.BundleIso (TBpull D) TBdisc) := by
  haveI : Nonempty (Submission.Milnor.Vk (-2)) := inferInstance
  haveI : Nonempty (EuclideanSpace ℝ (Fin 8)) := inferInstance
  haveI : IsManifold Work.Milnor.mMSpace8 ∞ D.Glued := Work.Glue.glued_isManifold D
  obtain ⟨h1, h2⟩ := mfderiv_iota_symm D
  refine ⟨{ hom := fun b => homLM D b
            inv := fun b => invLM D b
            left_inv := fun b x => h1 b x
            right_inv := fun b y => h2 b y
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · refine (continuous_homLM D).congr (fun p => ?_)
    have hx : D.ιX p.1 ∈ D.homX.target := by
      rw [D.homX_target]; exact ⟨p.1, rfl⟩
    have heq : mfderivWithin Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm)
        D.homX.target (D.ιX p.1) =
        mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm) (D.ιX p.1) :=
      mfderivWithin_of_mem_nhds (D.homX.open_target.mem_nhds hx)
    show (tangentMapWithin Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm)
        D.homX.target (⟨D.ιX p.1, p.2⟩ : (Work.TangentClasses.tangentBundle
          Work.Milnor.mMSpace8 D.Glued).TotalSpace)) =
      (⟨p.1, (mfderiv Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 (⇑D.homX.symm)
        (D.ιX p.1)).toLinearMap p.2⟩ : TBdisc.TotalSpace)
    simp only [tangentMapWithin]
    rw [D.homX_symm_apply p.1, heq]
    rfl
  · exact continuous_invLM D

end

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

theorem tangentRestriction
    (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap
        (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
          (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) (Work.Agree.incl F hF))
      (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
        (Submission.Milnor.Vk (-2)))) :=
  tangentRestriction_datum (Work.Milnor.cappedDatum F hF)

end Work.Agree
