import Mathlib
import Submission.Work.Milnor.CapDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the second chart of the inverse capping map

`chartInvFormY e` is the second-chart formula for the inverse of the capping map
`capFunInv e : ℝ⁸ → Vk (-2)` (see `Work.Milnor.CapDefs`).  Writing
`p = (clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))` for the coordinates of
`e⁻¹ (w/‖w‖)` in the second chart of `Mk (-2)`, it reads

`chartInvFormY e w = (p.1, ‖vkModelIso w‖ • ((p.2 : QS3) : ℍ))`.

On the set of points `w` with `‖vkModelIso w‖ > 1/2` and with `e⁻¹ (w/‖w‖)` in the *second* chart
of `Mk (-2)` (i.e. in `range (clutchData (-2)).ιY`) this is a composite of smooth maps:

* `w ↦ vkModelIso w` — linear;
* `z ↦ unitOf z` — smooth on the exterior `capExterior = {1/2 < ‖z‖}` (`contMDiffOn_unitOf`);
* `z ↦ e.symm z` — a diffeomorphism;
* `p ↦ (clutchData (-2)).homY.symm p` — smooth on `(clutchData (-2)).homY.target`
  (`contMDiffOn_clutchHomYsymm`), which is exactly `range (clutchData (-2)).ιY`;
* and finally the two components `p ↦ p.1` and `p ↦ ((p.2 : QS3) : ℍ)` paired with the
  scalar factor `w ↦ ‖vkModelIso w‖`.

The main theorem `chartInvFormY_contMDiffOn` is the second-chart half of the smoothness of
`capFunInv`; the first-chart half is `Work.Milnor.chartInvFormX_contMDiffOn`.
-/

open scoped Manifold ContDiff Topology
open Submission.Milnor

namespace Work.Milnor

theorem chartInvFormY_contMDiffOn (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) : ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 Work.Milnor.smLevel (Work.Milnor.chartInvFormY e) {w : Submission.Milnor.MSpace8 | 1 / 2 < ‖Work.Milnor.vkModelIso w‖ ∧ e.symm (Work.Milnor.unitOf (Work.Milnor.vkModelIso w)) ∈ Set.range (Submission.Milnor.clutchData (-2)).ιY} := by
  set S : Set MSpace8 := {w : MSpace8 | 1 / 2 < ‖vkModelIso w‖ ∧
    e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY} with hS
  -- `vkModelIso` is a linear map, hence smooth.
  have hVK : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun w : MSpace8 => vkModelIso w) :=
    vkModelIso.contDiff.contMDiff
  -- The normalisation `z ↦ z/‖z‖` is smooth on the exterior of the ball of radius `1/2`.
  have hU : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 7) ∞ (fun w : MSpace8 => unitOf (vkModelIso w))
      (vkModelIso ⁻¹' capExterior) :=
    contMDiffOn_unitOf.comp hVK.contMDiffOn (fun x hx => hx)
  -- `e.symm` is smooth, so it can be composed on the left.
  have h2 : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => e.symm (unitOf (vkModelIso w))) (vkModelIso ⁻¹' capExterior) :=
    (Diffeomorph.contMDiff_invFun e).contMDiffOn.comp hU (t := Set.univ) (fun x hx => trivial)
  -- The target of the second chart of `Mk (-2)` is the range of `ιY`.
  have hyT : (clutchData (-2)).homY.target = Set.range (clutchData (-2)).ιY :=
    Submission.Glue.Data.homY_target (clutchData (-2))
  -- Hence the second chart of the inverse capping map, as a map into `ℝ⁴ × S³`, is smooth.
  have hF : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => (clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))) S :=
    (contMDiffOn_clutchHomYsymm (-2)).comp (h2.mono (fun x hx => hx.1)) (by
      intro x hx
      rw [hyT]
      exact hx.2)
  -- Its first coordinate, as a map into `ℝ⁴`.
  have h1m : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 4) ∞
      (fun w : MSpace8 => ((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).1) S :=
    (contMDiff_fst (n := ∞)).contMDiffOn.comp hF (t := Set.univ) (fun x hx => trivial)
  have h1 : ContDiffOn ℝ ∞
      (fun w : MSpace8 => ((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).1) S :=
    contMDiffOn_iff_contDiffOn.mp h1m
  -- Its second coordinate, as a map into `S³`.
  have h2m : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 3) ∞
      (fun w : MSpace8 => ((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).2) S :=
    (contMDiff_snd (n := ∞)).contMDiffOn.comp hF (t := Set.univ) (fun x hx => trivial)
  -- ... followed by the (smooth) inclusion of `S³` into `ℍ`.
  have h2c : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun w : MSpace8 =>
        ((((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ)) S :=
    (contMDiff_coe_sphere (E := Quaternion ℝ) (n := 3) (m := ∞)).contMDiffOn.comp h2m
      (t := Set.univ) (fun x hx => trivial)
  have h2b : ContDiffOn ℝ ∞
      (fun w : MSpace8 =>
        ((((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ)) S :=
    contMDiffOn_iff_contDiffOn.mp h2c
  -- The scalar factor `‖vkModelIso w‖` is smooth, being nonzero on `S`.
  have h3c : ContDiffOn ℝ ∞ (fun w : MSpace8 => ‖vkModelIso w‖) S :=
    (vkModelIso.contDiff.contDiffOn).norm ℝ (fun w hw => by
      rw [← norm_ne_zero_iff]
      linarith [hw.1])
  -- Multiplying the fibre coordinate by that factor preserves smoothness.
  have h4 : ContDiffOn ℝ ∞ (fun w : MSpace8 =>
      ‖vkModelIso w‖ • ((((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ)) S :=
    h3c.smul h2b
  -- This is exactly `chartInvFormY e`.
  have hpair := h1.prodMk h4
  exact contMDiffOn_iff_contDiffOn.mpr hpair

end Work.Milnor
