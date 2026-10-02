import Mathlib
import Submission.Work.Milnor.CapDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the first chart form of the capping map

`chartFormX e` is the explicit chartwise formula for the capping map `capFun e` on the first chart
of the disc bundle: for `a : ℝ⁴ × ℍ` it is
`‖a.2‖ • vkModelIso.symm (e (ιX (a.1, qDir a.2)))`, i.e. normalise the fibre coordinate, apply the
diffeomorphism `e : Mk (-2) ≃ S⁷`, and rescale by `‖a.2‖`.

This file proves that this formula is smooth on the exterior of the ball of radius `1/2` in the
fibre, `{a | 1/2 < ‖a.2‖}` — the region where the normalisation `a ↦ qDir a.2` is smooth.
-/

open scoped Manifold ContDiff
open Submission.Milnor

set_option linter.style.haveILetI false

namespace Work.Milnor

theorem chartFormX_contMDiffOn (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) : ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 Work.Milnor.smLevel (Work.Milnor.chartFormX e) {a : Submission.Milnor.MSpace8 | 1 / 2 < ‖a.2‖} := by
  -- the model `𝓡 7` on `S⁷ ⊆ ℝ⁸`, needed for `contMDiff_coe_sphere`
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]⟩
  -- the exterior of the ball of radius `1/2` lies in `{a | a.2 ≠ 0}`
  have hS : {a : MSpace8 | 1 / 2 < ‖a.2‖} ⊆ (capFibreOpens : Set MSpace8) := by
    intro a ha
    change (1 / 2 : ℝ) < ‖a.2‖ at ha
    show a.2 ≠ 0
    intro h0
    rw [h0, norm_zero] at ha
    norm_num at ha
  -- the two components of the "normalised chart point" `a ↦ (a.1, qDir a.2)`
  have hfst : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 4) ∞ (fun a : MSpace8 => a.1)
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 4)) (Quaternion ℝ)).contMDiff).contMDiffOn
  have hqdir : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 3) ∞ (fun a : MSpace8 => qDir a.2)
      {a : MSpace8 | 1 / 2 < ‖a.2‖} := contMDiffOn_qDir_snd.mono hS
  have hb : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun a : MSpace8 => (a.1, qDir a.2)) {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    hfst.prodMk hqdir
  -- glue into the chart of `Mk (-2)`, apply the diffeomorphism, and read off the ambient `ℝ⁸`
  have hι : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun a : MSpace8 => (clutchData (-2)).ιX (a.1, qDir a.2)) {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    (contMDiff_clutchIotaX (-2)).comp_contMDiffOn hb
  have he : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 7) ∞
      (fun a : MSpace8 => e ((clutchData (-2)).ιX (a.1, qDir a.2))) {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    e.contMDiff.comp_contMDiffOn hι
  have hcoe : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun a : MSpace8 => ((e ((clutchData (-2)).ιX (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    (contMDiff_coe_sphere (n := 7) (m := ∞) (E := EuclideanSpace ℝ (Fin 8))).comp_contMDiffOn he
  -- identify `ℝ⁸` with the model space of the bundle, and rescale by `‖a.2‖`
  have hvk : ContDiffOn ℝ ∞ (fun a : MSpace8 =>
      vkModelIso.symm ((e ((clutchData (-2)).ιX (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    ((vkModelIso.symm.toContinuousLinearMap).contDiff).comp_contDiffOn
      (contMDiffOn_iff_contDiffOn.mp hcoe)
  have hnorm : ContDiffOn ℝ ∞ (fun a : MSpace8 => ‖a.2‖) {a : MSpace8 | 1 / 2 < ‖a.2‖} := by
    have hsnd : ContDiffOn ℝ ∞ (fun a : MSpace8 => a.2) {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
      contDiff_snd.contDiffOn
    refine ContDiffOn.norm ℝ hsnd (fun a ha => ?_)
    change (1 / 2 : ℝ) < ‖a.2‖ at ha
    intro h0
    rw [h0, norm_zero] at ha
    norm_num at ha
  have hsmul : ContDiffOn ℝ ∞ (fun a : MSpace8 =>
      ‖a.2‖ • vkModelIso.symm ((e ((clutchData (-2)).ιX (a.1, qDir a.2))) : EuclideanSpace ℝ (Fin 8)))
      {a : MSpace8 | 1 / 2 < ‖a.2‖} := hnorm.smul hvk
  refine contMDiffOn_iff_contDiffOn.mpr (hsmul.congr ?_)
  intro a ha
  rw [chartFormX]

end Work.Milnor
