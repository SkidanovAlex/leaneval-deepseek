import Mathlib
import Submission.Work.Milnor.CapCompact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the second chart of the inverse compact capping map

`chartInvFormKY e` is the second-chart formula for the inverse of the compact capping map
`capFunInvK e : ℝ⁸ → Vk (-2)` (see `Work.Milnor.CapCompact`).  Writing
`p = (clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))` for the coordinates of
`e⁻¹ (w/‖w‖)` in the second chart of `Mk (-2)`, it reads

`chartInvFormKY e w = (p.1, (‖vkModelIso w‖⁻¹ + 1/2) • ((p.2 : QS3) : ℍ))`.

Unlike the (non-compact) capping of `Work.Milnor.CapDefs`, the scalar here is the *inverting*
radius `‖z‖⁻¹ + 1/2`, so the formula is smooth wherever `vkModelIso w ≠ 0` (and not merely where
`‖vkModelIso w‖ > 1/2`).  Accordingly the smoothness of the direction map `z ↦ z/‖z‖` is needed on
the whole punctured space `capPunct = ℝ⁸ ∖ {0}` rather than only on the exterior `capExterior`.

The composite is
* `w ↦ vkModelIso w` — linear;
* `z ↦ unitOf z` — smooth on `capPunct` (`contMDiffOn_unitOf_punct` below);
* `z ↦ e.symm z` — a diffeomorphism;
* `p ↦ (clutchData (-2)).homY.symm p` — smooth on `(clutchData (-2)).homY.target`, exactly
  `range (clutchData (-2)).ιY`;
* and finally the two components `p ↦ p.1` and `p ↦ ((p.2 : QS3) : ℍ)` paired with the scalar
  factor `w ↦ ‖vkModelIso w‖⁻¹ + 1/2`.
-/

open scoped Manifold ContDiff Topology
open Submission.Milnor

namespace Work.Milnor

noncomputable section

/-- The direction map `z ↦ z/‖z‖` is smooth on the punctured space `ℝ⁸ ∖ {0}`, as a map
into `S⁷`.  (Compare `Work.Milnor.contMDiffOn_unitOf`, which only covers the exterior
`{1/2 < ‖z‖}`.) -/
theorem contMDiffOn_unitOf_punct :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 7) ∞ (fun z => unitOf z) capPunct := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) := ⟨by simp⟩
  have hdiff : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => ‖z‖⁻¹ • z) capPunct := by
    have hs : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => z) capPunct :=
      contDiff_id.contDiffOn
    have hn : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => ‖z‖) capPunct :=
      ContDiffOn.norm ℝ hs (fun z hz => ne_zero_of_mem_capPunct hz)
    exact (hn.inv (fun z hz => norm_ne_zero_iff.mpr (ne_zero_of_mem_capPunct hz))).smul hs
  have hcoe : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun z : EuclideanSpace ℝ (Fin 8) => ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)))
      capPunct :=
    (contMDiffOn_iff_contDiffOn.mpr hdiff).congr (fun z hz => coe_unitOf_of_ne
      (ne_zero_of_mem_capPunct hz))
  have hglob : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun z : ↥capPunctOpens => ((unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8)
        : EuclideanSpace ℝ (Fin 8))) := by
    intro z
    exact (contMDiffAt_subtype_iff (U := capPunctOpens)
      (f := fun z : EuclideanSpace ℝ (Fin 8) => ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)))
      (x := z)).mpr (hcoe.contMDiffAt (capPunctOpens.2.mem_nhds z.2))
  have hmem : ∀ z : ↥capPunctOpens,
      ((unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8) : EuclideanSpace ℝ (Fin 8))
        ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 := fun z => (unitOf _).2
  have hsphere : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 7) ∞
      (fun z : ↥capPunctOpens => unitOf (z : EuclideanSpace ℝ (Fin 8))) :=
    (ContMDiff.codRestrict_sphere (n := 7) hglob hmem).congr (fun z => Subtype.ext rfl)
  intro z hz
  exact ((contMDiffAt_subtype_iff (U := capPunctOpens)
    (f := fun z : EuclideanSpace ℝ (Fin 8) => unitOf z) (x := ⟨z, hz⟩)).mp
    (hsphere ⟨z, hz⟩)).contMDiffWithinAt

theorem chartInvFormKY_contMDiffOn (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) : ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 Work.Milnor.smLevel (Work.Milnor.chartInvFormKY e) {w : Submission.Milnor.MSpace8 | Work.Milnor.vkModelIso w ≠ 0 ∧ e.symm (Work.Milnor.unitOf (Work.Milnor.vkModelIso w)) ∈ Set.range (Submission.Milnor.clutchData (-2)).ιY} := by
  set S : Set MSpace8 := {w : MSpace8 | vkModelIso w ≠ 0 ∧
    e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιY} with hS
  -- `vkModelIso` is a linear map, hence smooth.
  have hVK : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun w : MSpace8 => vkModelIso w) :=
    vkModelIso.contDiff.contMDiff
  -- The normalisation `z ↦ z/‖z‖` is smooth on the punctured space.
  have hU : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 7) ∞ (fun w : MSpace8 => unitOf (vkModelIso w)) S :=
    contMDiffOn_unitOf_punct.comp hVK.contMDiffOn (fun x hx => hx.1)
  -- `e.symm` is smooth, so it can be composed on the left.
  have h2 : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => e.symm (unitOf (vkModelIso w))) S :=
    (Diffeomorph.contMDiff_invFun e).contMDiffOn.comp hU (t := Set.univ) (fun x hx => trivial)
  -- The target of the second chart of `Mk (-2)` is the range of `ιY`.
  have hyT : (clutchData (-2)).homY.target = Set.range (clutchData (-2)).ιY :=
    Submission.Glue.Data.homY_target (clutchData (-2))
  -- Hence the second chart of the inverse compact capping map, as a map into `ℝ⁴ × S³`, is smooth.
  have hF : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => (clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))) S :=
    (contMDiffOn_clutchHomYsymm (-2)).comp h2 (by
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
  -- The scalar factor `‖vkModelIso w‖⁻¹ + 1/2` is smooth, being defined on `S`.
  have hnorm : ContDiffOn ℝ ∞ (fun w : MSpace8 => ‖vkModelIso w‖) S :=
    (vkModelIso.contDiff.contDiffOn).norm ℝ (fun w hw => hw.1)
  have h3c : ContDiffOn ℝ ∞ (fun w : MSpace8 => ‖vkModelIso w‖⁻¹ + 1 / 2) S :=
    (hnorm.inv (fun w hw => norm_ne_zero_iff.mpr hw.1)).add contDiffOn_const
  -- Multiplying the fibre coordinate by that factor preserves smoothness.
  have h4 : ContDiffOn ℝ ∞ (fun w : MSpace8 =>
      (‖vkModelIso w‖⁻¹ + 1 / 2) • ((((clutchData (-2)).homY.symm (e.symm (unitOf (vkModelIso w)))).2 : QS3) : Quaternion ℝ)) S :=
    h3c.smul h2b
  -- This is exactly `chartInvFormKY e`.
  have hpair := h1.prodMk h4
  exact contMDiffOn_iff_contDiffOn.mpr hpair

end

end Work.Milnor
