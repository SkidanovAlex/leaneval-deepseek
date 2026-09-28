import Mathlib
import Submission.Work.Milnor.Model8
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.CollarHomotopy
import Submission.Work.Milnor.ScaleDefs
import Submission.Work.Milnor.UnitSphere
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.Homeo7
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.exists_collar_coordinates
import Submission.Work.Glue.mem_groupoid_of_contMDiffOn
import Submission.Work.Milnor.CapDefs
import Submission.Work.Milnor.chartFormX_contMDiffOn
import Submission.Work.Milnor.chartFormY_contMDiffOn
import Submission.Work.Milnor.chartInvFormX_contMDiffOn
import Submission.Work.Milnor.chartInvFormY_contMDiffOn

set_option synthInstance.maxHeartbeats 400000

/-!
# The capping datum for the disc bundle `Vk (-2)`

Given a diffeomorphism `e : Mk (-2) ≃ S⁷` of the sphere bundle of `ξ = Vk (-2)` with the unit
sphere, we construct the gluing data `D : CapData` of `Submission/NOTES.md` §9.3: the open collar
`{1/2 < ν} ⊆ Vk (-2)` is glued to the exterior `{1/2 < ‖z‖} ⊆ ℝ⁸` of the ball of radius `1/2` by
the diffeomorphism

  `p ↦ ν(p) • e(p/ν(p))`  (resp.  `z ↦ ‖z‖ • e⁻¹(z/‖z‖)`),

whose glued space is the closed `8`-manifold `X = D(ξ) ∪_e D⁸`.

The two maps, their inverse laws and the chartwise formulas are in
`Submission.Work.Milnor.CapDefs`; the four smoothness lemmas for the explicit chartwise formulas
(one per chart of `Mk (-2)`, in each direction) are `Work.Milnor.chartFormX_contMDiffOn`,
`Work.Milnor.chartFormY_contMDiffOn`, `Work.Milnor.chartInvFormX_contMDiffOn` and
`Work.Milnor.chartInvFormY_contMDiffOn`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology EuclideanSpace
open Submission.Milnor
open TopologicalSpace

noncomputable section

/-- The inverse capping map is smooth on the exterior of the ball, for the model structure
pushed forward to `ℝ⁸` along `vkModelIso`. -/
theorem contMDiffOn_pushed_capFunInv (e : Diffeomorph mE4E3 mE7 (Mk (-2)) Sph8 smLevel) :
    ContMDiffOn mMSpace8 mMSpace8 smLevel (capFunInv e) capExterior := by
  have hSX : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun w => capFunInv e (vkModelIso w))
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} := by
    refine ((contMDiff_iotaX (-2)).contMDiffOn (s := Set.univ)).comp
      (chartInvFormX_contMDiffOn e) (fun w _ => Set.mem_univ _) |>.congr (fun w hw => ?_)
    exact capFunInv_eq_ιX' e hw.1 hw.2
  have hSY : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun w => capFunInv e (vkModelIso w))
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY} := by
    refine ((contMDiff_iotaY (-2)).contMDiffOn (s := Set.univ)).comp
      (chartInvFormY_contMDiffOn e) (fun w _ => Set.mem_univ _) |>.congr (fun w hw => ?_)
    exact capFunInv_eq_ιY' e hw.1 hw.2
  have hcover : vkModelIso ⁻¹' capExterior ⊆
      ({w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} ∪
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY}) := by
    intro w hw
    have h1 : 1 / 2 < ‖vkModelIso w‖ := hw
    rcases (show e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX ∪
        Set.range (clutchData (-2)).ιY from by
      rw [(clutchData (-2)).range_ιX_union_range_ιY]; exact Set.mem_univ _) with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h⟩
  have hB : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun w => capFunInv e (vkModelIso w))
      (vkModelIso ⁻¹' capExterior) := by
    intro w hw
    have hT : {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖} ∈ 𝓝 w :=
      (isOpen_lt continuous_const (continuous_norm.comp vkModelIso.continuous)).mem_nhds hw
    have hcont : ContinuousAt (fun w : MSpace8 => e.symm (unitOf (vkModelIso w))) w := by
      have h1 : ContMDiffAt mMSpace8 mE7 smLevel (fun w : MSpace8 => unitOf (vkModelIso w)) w :=
        (contMDiffOn_unitOf.contMDiffAt (isOpen_capExterior.mem_nhds hw)).comp w
          (contMDiff_vkModelIso.contMDiffAt)
      exact (e.symm.contMDiff_toFun.contMDiffAt).comp w h1 |>.continuousAt
    rcases hcover hw with h | h
    · have hG : {w : MSpace8 | e.symm (unitOf (vkModelIso w)) ∈
          Set.range (clutchData (-2)).ιX} ∈ 𝓝 w :=
        hcont.preimage_mem_nhds (((clutchData (-2)).isOpenMap_ιX.isOpen_range).mem_nhds h.2)
      exact ((hSX w h).contMDiffAt (Filter.inter_mem hT hG)).contMDiffWithinAt
    · have hG : {w : MSpace8 | e.symm (unitOf (vkModelIso w)) ∈
          Set.range (clutchData (-2)).ιY} ∈ 𝓝 w :=
        hcont.preimage_mem_nhds (((clutchData (-2)).isOpenMap_ιY.isOpen_range).mem_nhds h.2)
      exact ((hSY w h).contMDiffAt (Filter.inter_mem hT hG)).contMDiffWithinAt
  have hfin : ContMDiffOn mMSpace8 mMSpace8 smLevel
      (fun y => capFunInv e (vkModelIso (vkModelIso.symm y))) capExterior :=
    hB.comp (contMDiff_vkModelIsoSymm_pushed.contMDiffOn (s := capExterior))
      (fun y hy => by
        rw [Set.mem_preimage, Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
        exact hy)
  refine hfin.congr (fun y _ => ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The capping map is smooth on the collar, for the model structure pushed forward to `ℝ⁸`. -/
theorem contMDiffOn_pushed_capFun (e : Diffeomorph mE4E3 mE7 (Mk (-2)) Sph8 smLevel) :
    ContMDiffOn mMSpace8 mMSpace8 smLevel (capFun e) (collar (-2)) := by
  have hsetX : (vData (-2)).ιX ⁻¹' collar (-2) = {a : MSpace8 | 1 / 2 < ‖a.2‖} := by
    ext a
    rw [Set.mem_preimage, mem_collar, fibreNormFun_ιX]
    exact Iff.rfl
  have hsetY : (vData (-2)).ιY ⁻¹' collar (-2) = {a : MSpace8 | 1 / 2 < ‖a.2‖} := by
    ext a
    rw [Set.mem_preimage, mem_collar, fibreNormFun_ιY]
    exact Iff.rfl
  have hX : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun a => capFun e ((vData (-2)).ιX a))
      ((vData (-2)).ιX ⁻¹' collar (-2)) := by
    rw [hsetX]
    refine ((contMDiff_vkModelIso_pushed.contMDiffOn (s := Set.univ)).comp
      (chartFormX_contMDiffOn e) (fun a _ => Set.mem_univ _)).congr (fun a ha => ?_)
    exact capFun_ιX' e a ha
  have hY : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun a => capFun e ((vData (-2)).ιY a))
      ((vData (-2)).ιY ⁻¹' collar (-2)) := by
    rw [hsetY]
    refine ((contMDiff_vkModelIso_pushed.contMDiffOn (s := Set.univ)).comp
      (chartFormY_contMDiffOn e) (fun a _ => Set.mem_univ _)).congr (fun a ha => ?_)
    exact capFun_ιY' e a ha
  intro z hz
  rcases hout : Quotient.out z with x | y
  · have hzeq : z = (vData (-2)).ιX x := by rw [← Quotient.out_eq z, hout]; rfl
    have hx_mem : x ∈ (vData (-2)).ιX ⁻¹' collar (-2) := by
      rw [Set.mem_preimage, ← hzeq]; exact hz
    have hnhds : (vData (-2)).ιX ⁻¹' collar (-2) ∈ 𝓝 x :=
      (isOpen_collar (-2)).preimage (vData (-2)).continuous_ιX |>.mem_nhds hx_mem
    have hcx : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFun e ((vData (-2)).ιX a)) x := (hX x hx_mem).contMDiffAt hnhds
    have hsymm_x : (vData (-2)).homX.symm z = x := by
      rw [hzeq]; exact (vData (-2)).homX_symm_apply x
    have hcx' : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFun e ((vData (-2)).ιX a)) ((vData (-2)).homX.symm z) := by
      rw [hsymm_x]; exact hcx
    have hsymm_nhds : (vData (-2)).homX.target ∈ 𝓝 z := by
      rw [Submission.Glue.Data.homX_target]
      exact ((vData (-2)).isOpenMap_ιX.isOpen_range).mem_nhds ⟨x, hzeq.symm⟩
    have hsymm : ContMDiffAt mMSpace8 mMSpace8 smLevel (⇑(vData (-2)).homX.symm) z :=
      (contMDiffOn_homXsymm (-2)).contMDiffAt hsymm_nhds
    refine ((hcx'.comp z hsymm).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((vData (-2)).isOpenMap_ιX.isOpen_range).mem_nhds
      (show z ∈ Set.range (vData (-2)).ιX from ⟨x, hzeq.symm⟩)] with p hp
    obtain ⟨a, rfl⟩ := hp
    show capFun e ((vData (-2)).ιX a)
      = capFun e ((vData (-2)).ιX ((vData (-2)).homX.symm ((vData (-2)).ιX a)))
    rw [(vData (-2)).homX_symm_apply a]
  · have hzeq : z = (vData (-2)).ιY y := by rw [← Quotient.out_eq z, hout]; rfl
    have hy_mem : y ∈ (vData (-2)).ιY ⁻¹' collar (-2) := by
      rw [Set.mem_preimage, ← hzeq]; exact hz
    have hnhds : (vData (-2)).ιY ⁻¹' collar (-2) ∈ 𝓝 y :=
      (isOpen_collar (-2)).preimage (vData (-2)).continuous_ιY |>.mem_nhds hy_mem
    have hcy : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFun e ((vData (-2)).ιY a)) y := (hY y hy_mem).contMDiffAt hnhds
    have hsymm_y : (vData (-2)).homY.symm z = y := by
      rw [hzeq]; exact (vData (-2)).homY_symm_apply y
    have hcy' : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFun e ((vData (-2)).ιY a)) ((vData (-2)).homY.symm z) := by
      rw [hsymm_y]; exact hcy
    have hsymm_nhds : (vData (-2)).homY.target ∈ 𝓝 z := by
      rw [Submission.Glue.Data.homY_target]
      exact ((vData (-2)).isOpenMap_ιY.isOpen_range).mem_nhds ⟨y, hzeq.symm⟩
    have hsymm : ContMDiffAt mMSpace8 mMSpace8 smLevel (⇑(vData (-2)).homY.symm) z :=
      (contMDiffOn_homYsymm (-2)).contMDiffAt hsymm_nhds
    refine ((hcy'.comp z hsymm).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((vData (-2)).isOpenMap_ιY.isOpen_range).mem_nhds
      (show z ∈ Set.range (vData (-2)).ιY from ⟨y, hzeq.symm⟩)] with p hp
    obtain ⟨a, rfl⟩ := hp
    show capFun e ((vData (-2)).ιY a)
      = capFun e ((vData (-2)).ιY ((vData (-2)).homY.symm ((vData (-2)).ιY a)))
    rw [(vData (-2)).homY_symm_apply a]

/-- **The capping datum**, from a diffeomorphism of the sphere bundle `Mk (-2)` with `S⁷`. -/
theorem exists_capData_aux (e : Diffeomorph mE4E3 mE7 (Mk (-2)) Sph8 smLevel) :
    ∃ D : CapData, IsCappingDatum (⇑e) D := by
  have hφ := contMDiffOn_pushed_capFun e
  have hφ' := contMDiffOn_pushed_capFunInv e
  let φ : OpenPartialHomeomorph (Vk (-2)) (EuclideanSpace ℝ (Fin 8)) :=
    { toFun := capFun e
      invFun := capFunInv e
      source := collar (-2)
      target := capExterior
      map_source' := fun p hp => capFun_mem e hp
      map_target' := fun z hz => capFunInv_mem e hz
      left_inv' := fun p hp => capFunInv_capFun e hp
      right_inv' := fun z hz => capFun_capFunInv e hz
      continuousOn_toFun := hφ.continuousOn
      continuousOn_invFun := hφ'.continuousOn
      open_source := isOpen_collar (-2)
      open_target := isOpen_capExterior }
  let D : CapData :=
    { U := collar (-2)
      V := capExterior
      isOpen_U := isOpen_collar (-2)
      isOpen_V := isOpen_capExterior
      φ := φ
      source_φ := rfl
      target_φ := rfl
      mem_groupoid := Work.Glue.mem_groupoid_of_contMDiffOn hφ hφ' }
  refine ⟨D, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro q
    show (φ : OpenPartialHomeomorph (Vk (-2)) (EuclideanSpace ℝ (Fin 8))) (mkToVkFun (-2) q)
      = (e q : EuclideanSpace ℝ (Fin 8))
    exact capFun_mkToVkFun e q

theorem exists_capData
    (F : Submission.Milnor.Mk (-2) → Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    ∃ D : Work.Milnor.CapData, Work.Milnor.IsCappingDatum F D := by
  obtain ⟨e, he⟩ := hF
  obtain ⟨D, hD⟩ := exists_capData_aux e
  rw [he] at hD
  exact ⟨D, hD⟩

end

end Work.Milnor
