import Mathlib
import Submission.Work.Milnor.CapDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

/-- The second chartwise formula for the capping map,
`a ↦ ‖a.2‖ • vkModelIso.symm (e (ιY (a.1, a.2/‖a.2‖)))`, is smooth on the collar
`{a | 1/2 < ‖a.2‖}` of the disc bundle. -/
theorem chartFormY_contMDiffOn (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) : ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 Work.Milnor.smLevel (Work.Milnor.chartFormY e) {a : Submission.Milnor.MSpace8 | 1 / 2 < ‖a.2‖} := by
  have hsub : ∀ a : MSpace8, (1 : ℝ) / 2 < ‖a.2‖ → a.2 ≠ 0 := by
    intro a ha h0
    rw [h0, norm_zero] at ha
    norm_num at ha
  -- the first chart coordinate `a ↦ a.1`
  have hfst : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 4) ∞ (fun a : MSpace8 => a.1)
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    (ContinuousLinearMap.contMDiff
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 4)) (Quaternion ℝ))).contMDiffOn
  -- the normalised fibre coordinate `a ↦ a.2/‖a.2‖`
  have hqd : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 3) ∞ (fun a : MSpace8 => qDir a.2)
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    contMDiffOn_qDir_snd.mono (fun a ha => hsub a ha)
  have hpair := hfst.prodMk hqd
  -- the second chart of the disc bundle
  have hiY : ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞
      (fun p : MSpace => (clutchData (-2)).ιY p) Set.univ :=
    (contMDiff_clutchIotaY (-2)).contMDiffOn
  have h1 := hiY.comp hpair (Set.subset_univ _)
  -- the diffeomorphism `e`, then the inclusion `S⁷ ⊆ ℝ⁸`, then the linear isometry
  have h2 := (Diffeomorph.contMDiff e).comp_contMDiffOn h1
  -- the inclusion `S⁷ ⊆ ℝ⁸` (a specialisation of `contMDiff_coe_sphere`)
  have hcoe : ContMDiff (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (Subtype.val : Sph8 → EuclideanSpace ℝ (Fin 8)) := by
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) := ⟨by simp⟩
    exact contMDiff_coe_sphere
  have h3 := hcoe.comp_contMDiffOn h2
  have h4 := (ContinuousLinearMap.contMDiff
    (vkModelIso.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] MSpace8)).comp_contMDiffOn h3
  -- multiplication by the fibre norm `‖a.2‖`
  have hsnd : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, Quaternion ℝ) ∞ (fun a : MSpace8 => a.2)
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    (ContinuousLinearMap.contMDiff
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4)) (Quaternion ℝ))).contMDiffOn
  have hnorm : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, ℝ) ∞ (fun a : MSpace8 => ‖a.2‖)
      {a : MSpace8 | 1 / 2 < ‖a.2‖} :=
    contMDiffOn_iff_contDiffOn.mpr
      ((contMDiffOn_iff_contDiffOn.mp hsnd).norm ℝ (fun a ha => hsub a ha))
  exact hnorm.smul h4

end Work.Milnor
