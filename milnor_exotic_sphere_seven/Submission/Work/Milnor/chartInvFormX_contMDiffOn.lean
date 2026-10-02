import Mathlib
import Submission.Work.Milnor.CapDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open scoped Manifold ContDiff Topology EuclideanSpace
open Submission.Milnor
open Set

noncomputable section

theorem chartInvFormX_contMDiffOn
    (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) :
    ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 Work.Milnor.smLevel (Work.Milnor.chartInvFormX e)
      {w : Submission.Milnor.MSpace8 | 1 / 2 < ‖Work.Milnor.vkModelIso w‖ ∧
        e.symm (Work.Milnor.unitOf (Work.Milnor.vkModelIso w))
          ∈ Set.range (Submission.Milnor.clutchData (-2)).ιX} := by
  have hlin : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun w : MSpace8 => vkModelIso w) :=
    (ContinuousLinearEquiv.contDiff vkModelIso).contMDiff
  have hunit : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 7) ∞
      (fun w : MSpace8 => unitOf (vkModelIso w))
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    contMDiffOn_unitOf.comp hlin.contMDiffOn (fun w hw => by
      rw [Set.mem_preimage, mem_capExterior_iff]; exact hw.1)
  have hΦ : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => e.symm (unitOf (vkModelIso w)))
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    (e.symm.contMDiff).comp_contMDiffOn hunit
  have hF : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => (clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w))))
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    (contMDiffOn_clutchHomXsymm (-2)).comp hΦ (fun w hw => by
      rw [Set.mem_preimage, Submission.Glue.Data.homX_target]; exact hw.2)
  have hsndsmooth : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 3) ∞
      (fun w : MSpace8 => ((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).2)
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    fun w hw => (hF w hw).snd
  have hcoe' : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun w : MSpace8 =>
        (((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).2 : Quaternion ℝ))
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    (contMDiff_coe_sphere (E := Quaternion ℝ) (n := 3) (m := ∞)).comp_contMDiffOn hsndsmooth
  have hcoef : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, ℝ) ∞ (fun w : MSpace8 => ‖vkModelIso w‖)
      {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} := by
    rw [contMDiffOn_iff_contDiffOn]
    exact ContDiffOn.norm (𝕜 := ℝ)
      ((ContinuousLinearEquiv.contDiff vkModelIso).contDiffOn)
      (fun w hw => norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hw.1)))
  rw [contMDiffOn_prod_module_iff]
  refine ⟨?_, ?_⟩
  · have h1 : (Prod.fst ∘ chartInvFormX e)
        = (fun w : MSpace8 => ((clutchData (-2)).homX.symm
            (e.symm (unitOf (vkModelIso w)))).1) := rfl
    rw [h1]
    intro w hw
    exact (hF w hw).fst
  · have h2 : (Prod.snd ∘ chartInvFormX e)
        = (fun w : MSpace8 => ‖vkModelIso w‖ •
            (((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).2 : Quaternion ℝ)) := rfl
    rw [h2]
    exact hcoef.smul hcoe'

end

end Work.Milnor
