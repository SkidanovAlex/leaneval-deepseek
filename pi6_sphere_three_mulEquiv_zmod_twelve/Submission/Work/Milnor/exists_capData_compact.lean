import Mathlib
import Submission.Work.Milnor.CapCompact
import Submission.Work.Milnor.exists_capData
import Submission.Work.Milnor.chartFormKX_contMDiffOn
import Submission.Work.Milnor.chartFormKY_contMDiffOn
import Submission.Work.Milnor.chartInvFormKX_contMDiffOn
import Submission.Work.Milnor.chartInvFormKY_contMDiffOn

set_option synthInstance.maxHeartbeats 400000

/-!
# The compact capping datum exists

`Submission/Work/Milnor/CapCompact.lean` defines the *compact* capping map
`capFunK e : Vk (-2) → ℝ⁸`, the involution of the collar `{1/2 < ν} ⊆ Vk (-2)` onto the punctured
space `capPunct = ℝ⁸ ∖ {0}` given by `p ↦ (ν p - 1/2)⁻¹ • e (ψ p)`, together with its inverse
`capFunInvK e`, and packages them as the open partial homeomorphism `capPhiK e`.

Here we show that this map is a diffeomorphism for the two smooth structures (that of the disc
bundle `Vk (-2)` and the model structure on `ℝ⁸` pushed forward along `vkModelIso`), so that it is
a legitimate gluing datum `D : CapData`, and hence that a *compact* capping datum exists for the
disc bundle:

* `contMDiffOn_pushed_capFunK` — `capFunK e` is `C^∞` on the collar;
* `contMDiffOn_pushed_capFunInvK` — `capFunInvK e` is `C^∞` on the punctured space;
* `exists_capData_compact` — the datum `capPhiK e` satisfies `IsCompactCapping e`.

Both smoothness statements are proved chart by chart, exactly as for the non-compact capping map
of `Submission/Work/Milnor/exists_capData.lean`: the four explicit chartwise formulas
`chartFormKX`, `chartFormKY`, `chartInvFormKX`, `chartInvFormKY` are smooth
(`Work.Milnor.chartFormKX_contMDiffOn` and friends), and smoothness transfers through the charts
`homX`, `homY` of the glued bundle and the linear isometry `vkModelIso`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology EuclideanSpace
open Submission.Milnor
open scoped Classical

noncomputable section

open TopologicalSpace

/-- The compact capping map is smooth on the collar, for the model structure pushed forward
from the standard one along `vkModelIso`. -/
theorem contMDiffOn_pushed_capFunK (e : Diffeomorph mE4E3 mE7 (Mk (-2)) Sph8 smLevel) :
    ContMDiffOn mMSpace8 mMSpace8 smLevel (capFunK e) (collar (-2)) := by
  have hsetX : (vData (-2)).ιX ⁻¹' collar (-2) = {a : MSpace8 | 1 / 2 < ‖a.2‖} := by
    ext a
    rw [Set.mem_preimage, mem_collar, fibreNormFun_ιX]
    exact Iff.rfl
  have hsetY : (vData (-2)).ιY ⁻¹' collar (-2) = {a : MSpace8 | 1 / 2 < ‖a.2‖} := by
    ext a
    rw [Set.mem_preimage, mem_collar, fibreNormFun_ιY]
    exact Iff.rfl
  have hX : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun a => capFunK e ((vData (-2)).ιX a))
      ((vData (-2)).ιX ⁻¹' collar (-2)) := by
    rw [hsetX]
    refine ((contMDiff_vkModelIso_pushed.contMDiffOn (s := Set.univ)).comp
      (chartFormKX_contMDiffOn e) (fun a _ => Set.mem_univ _)).congr (fun a ha => ?_)
    exact capFunK_ιX' e a ha
  have hY : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun a => capFunK e ((vData (-2)).ιY a))
      ((vData (-2)).ιY ⁻¹' collar (-2)) := by
    rw [hsetY]
    refine ((contMDiff_vkModelIso_pushed.contMDiffOn (s := Set.univ)).comp
      (chartFormKY_contMDiffOn e) (fun a _ => Set.mem_univ _)).congr (fun a ha => ?_)
    exact capFunK_ιY' e a ha
  intro z hz
  rcases hout : Quotient.out z with x | y
  · have hzeq : z = (vData (-2)).ιX x := by rw [← Quotient.out_eq z, hout]; rfl
    have hx_mem : x ∈ (vData (-2)).ιX ⁻¹' collar (-2) := by
      rw [Set.mem_preimage, ← hzeq]; exact hz
    have hnhds : (vData (-2)).ιX ⁻¹' collar (-2) ∈ 𝓝 x :=
      (isOpen_collar (-2)).preimage (vData (-2)).continuous_ιX |>.mem_nhds hx_mem
    have hcx : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFunK e ((vData (-2)).ιX a)) x := (hX x hx_mem).contMDiffAt hnhds
    have hsymm_x : (vData (-2)).homX.symm z = x := by
      rw [hzeq]; exact (vData (-2)).homX_symm_apply x
    have hcx' : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFunK e ((vData (-2)).ιX a)) ((vData (-2)).homX.symm z) := by
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
    show capFunK e ((vData (-2)).ιX a)
      = capFunK e ((vData (-2)).ιX ((vData (-2)).homX.symm ((vData (-2)).ιX a)))
    rw [(vData (-2)).homX_symm_apply a]
  · have hzeq : z = (vData (-2)).ιY y := by rw [← Quotient.out_eq z, hout]; rfl
    have hy_mem : y ∈ (vData (-2)).ιY ⁻¹' collar (-2) := by
      rw [Set.mem_preimage, ← hzeq]; exact hz
    have hnhds : (vData (-2)).ιY ⁻¹' collar (-2) ∈ 𝓝 y :=
      (isOpen_collar (-2)).preimage (vData (-2)).continuous_ιY |>.mem_nhds hy_mem
    have hcy : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFunK e ((vData (-2)).ιY a)) y := (hY y hy_mem).contMDiffAt hnhds
    have hsymm_y : (vData (-2)).homY.symm z = y := by
      rw [hzeq]; exact (vData (-2)).homY_symm_apply y
    have hcy' : ContMDiffAt mMSpace8 mMSpace8 smLevel
        (fun a => capFunK e ((vData (-2)).ιY a)) ((vData (-2)).homY.symm z) := by
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
    show capFunK e ((vData (-2)).ιY a)
      = capFunK e ((vData (-2)).ιY ((vData (-2)).homY.symm ((vData (-2)).ιY a)))
    rw [(vData (-2)).homY_symm_apply a]

/-- The inverse compact capping map is smooth on the punctured space, for the model structure
pushed forward from the standard one along `vkModelIso`. -/
theorem contMDiffOn_pushed_capFunInvK (e : Diffeomorph mE4E3 mE7 (Mk (-2)) Sph8 smLevel) :
    ContMDiffOn mMSpace8 mMSpace8 smLevel (capFunInvK e) capPunct := by
  have hSX : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun w => capFunInvK e (vkModelIso w))
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} := by
    refine ((contMDiff_iotaX (-2)).contMDiffOn (s := Set.univ)).comp
      (chartInvFormKX_contMDiffOn e) (fun w _ => Set.mem_univ _) |>.congr (fun w hw => ?_)
    exact capFunInvK_eq_ιX' e hw.1 hw.2
  have hSY : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun w => capFunInvK e (vkModelIso w))
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY} := by
    refine ((contMDiff_iotaY (-2)).contMDiffOn (s := Set.univ)).comp
      (chartInvFormKY_contMDiffOn e) (fun w _ => Set.mem_univ _) |>.congr (fun w hw => ?_)
    exact capFunInvK_eq_ιY' e hw.1 hw.2
  have hcover : vkModelIso ⁻¹' capPunct ⊆
      ({w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} ∪
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY}) := by
    intro w hw
    have h1 : vkModelIso w ≠ 0 := hw
    rcases (show e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX ∪
        Set.range (clutchData (-2)).ιY from by
      rw [(clutchData (-2)).range_ιX_union_range_ιY]; exact Set.mem_univ _) with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h⟩
  have hB : ContMDiffOn mMSpace8 mMSpace8 smLevel (fun w => capFunInvK e (vkModelIso w))
      (vkModelIso ⁻¹' capPunct) := by
    intro w hw
    have hT : {w : MSpace8 | vkModelIso w ≠ 0} ∈ 𝓝 w :=
      (isOpen_ne_fun vkModelIso.continuous continuous_const).mem_nhds hw
    have hcontU : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 8) => unitOf z) capPunct := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact continuous_unitOf_punct
    have hcomp : ContinuousAt (fun w : MSpace8 => unitOf (vkModelIso w)) w :=
      (hcontU.continuousAt (isOpen_capPunct.mem_nhds hw)).comp
        (vkModelIso.continuous.continuousAt)
    have hcont : ContinuousAt (fun w : MSpace8 => e.symm (unitOf (vkModelIso w))) w :=
      (e.symm.contMDiff.continuous.continuousAt).comp hcomp
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
      (fun y => capFunInvK e (vkModelIso (vkModelIso.symm y))) capPunct :=
    hB.comp (contMDiff_vkModelIsoSymm_pushed.contMDiffOn (s := capPunct))
      (fun y hy => by
        rw [Set.mem_preimage, Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
        exact hy)
  refine hfin.congr (fun y _ => ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- **The compact capping datum** exists as soon as the sphere bundle `Mk (-2)` is diffeomorphic
to `S⁷`: the gluing datum whose open sets are the collar `{1/2 < ν} ⊆ Vk (-2)` and the punctured
space `ℝ⁸ ∖ {0}`, glued by `capFunK e`. -/
theorem exists_capData_compact_aux (e : Diffeomorph mE4E3 mE7 (Mk (-2)) Sph8 smLevel) :
    ∃ D : CapData, IsCompactCapping e D := by
  have hφ := contMDiffOn_pushed_capFunK e
  have hφ' := contMDiffOn_pushed_capFunInvK e
  let φ : OpenPartialHomeomorph (Vk (-2)) (EuclideanSpace ℝ (Fin 8)) := capPhiK e
  let D : CapData :=
    { U := collar (-2)
      V := capPunct
      isOpen_U := isOpen_collar (-2)
      isOpen_V := isOpen_capPunct
      φ := φ
      source_φ := rfl
      target_φ := rfl
      mem_groupoid := Work.Glue.mem_groupoid_of_contMDiffOn hφ hφ' }
  refine ⟨D, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro p
    rfl

theorem exists_capData_compact (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) :
    ∃ D : Work.Milnor.CapData, Work.Milnor.IsCompactCapping e D :=
  exists_capData_compact_aux e

end

end Work.Milnor
