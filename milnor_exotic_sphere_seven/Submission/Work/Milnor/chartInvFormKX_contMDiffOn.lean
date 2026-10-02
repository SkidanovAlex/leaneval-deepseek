import Mathlib
import Submission.Work.Milnor.CapCompact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the first chart of the inverse compact capping map

`chartInvFormKX e` is the explicit first-chart formula for the inverse of the compact capping
map `capFunInvK e` (see `Work.Milnor.CapCompact`).  Writing
`p = (clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))` for the coordinates of
`e⁻¹ (vkModelIso w/‖vkModelIso w‖)` in the first chart of `Mk (-2)`, it reads

`chartInvFormKX e w = (p.1, (‖vkModelIso w‖⁻¹ + 1/2) • ((p.2 : QS3) : ℍ))`.

On the set of points `w` with `vkModelIso w ≠ 0` and with `e⁻¹ (unitOf (vkModelIso w))` in the
*first* chart of `Mk (-2)` (i.e. in `range (clutchData (-2)).ιX`) this is a composite of smooth
maps:

* `w ↦ vkModelIso w` — linear;
* `z ↦ unitOf z` — smooth away from `0` (`contMDiffOn_unitOf_ne_zero`);
* `z ↦ e.symm z` — a diffeomorphism;
* `p ↦ (clutchData (-2)).homX.symm p` — smooth on `(clutchData (-2)).homX.target`
  (`contMDiffOn_clutchHomXsymm`), which is exactly `range (clutchData (-2)).ιX`;
* and finally the two components `p ↦ p.1` and `p ↦ ((p.2 : QS3) : ℍ)` paired with the
  scalar factor `w ↦ ‖vkModelIso w‖⁻¹ + 1/2`.
-/

open scoped Manifold ContDiff Topology EuclideanSpace
open Submission.Milnor

namespace Work.Milnor

noncomputable section

/-- The direction map `z ↦ z/‖z‖` is smooth away from the origin, as a map into `S⁷`. -/
theorem contMDiffOn_unitOf_ne_zero :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 7) ∞ (fun z => unitOf z)
      ({z : EuclideanSpace ℝ (Fin 8) | z ≠ 0}) := by
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 8)) := ⟨{z | z ≠ 0}, isOpen_ne⟩
  have hdiff : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => ‖z‖⁻¹ • z)
      ({z : EuclideanSpace ℝ (Fin 8) | z ≠ 0}) := by
    have hs : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => z) {z | z ≠ 0} :=
      contDiff_id.contDiffOn
    have hn : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 8) => ‖z‖) {z | z ≠ 0} :=
      ContDiffOn.norm ℝ hs (fun z hz => hz)
    exact (hn.inv (fun z hz => norm_ne_zero_iff.mpr hz)).smul hs
  have hcoe : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun z : EuclideanSpace ℝ (Fin 8) => ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)))
      ({z : EuclideanSpace ℝ (Fin 8) | z ≠ 0}) :=
    (contMDiffOn_iff_contDiffOn.mpr hdiff).congr (fun z hz => coe_unitOf_of_ne hz)
  have hglob : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun z : ↥U => ((unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8)
        : EuclideanSpace ℝ (Fin 8))) := by
    intro z
    exact (contMDiffAt_subtype_iff (U := U)
      (f := fun z : EuclideanSpace ℝ (Fin 8) => ((unitOf z : Sph8) : EuclideanSpace ℝ (Fin 8)))
      (x := z)).mpr (hcoe.contMDiffAt (U.2.mem_nhds z.2))
  have hmem : ∀ z : ↥U,
      ((unitOf (z : EuclideanSpace ℝ (Fin 8)) : Sph8) : EuclideanSpace ℝ (Fin 8))
        ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1 := fun z => (unitOf _).2
  have hsphere : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (𝓡 7) ∞
      (fun z : ↥U => unitOf (z : EuclideanSpace ℝ (Fin 8))) :=
    (ContMDiff.codRestrict_sphere (n := 7) hglob hmem).congr (fun z => Subtype.ext rfl)
  intro z hz
  exact ((contMDiffAt_subtype_iff (U := U)
    (f := fun z : EuclideanSpace ℝ (Fin 8) => unitOf z) (x := ⟨z, hz⟩)).mp
    (hsphere ⟨z, hz⟩)).contMDiffWithinAt

theorem chartInvFormKX_contMDiffOn (e : Diffeomorph Work.Milnor.mE4E3 Work.Milnor.mE7 (Submission.Milnor.Mk (-2)) Work.Milnor.Sph8 Work.Milnor.smLevel) : ContMDiffOn Work.Milnor.mMSpace8 Work.Milnor.mMSpace8 Work.Milnor.smLevel (Work.Milnor.chartInvFormKX e) {w : Submission.Milnor.MSpace8 | Work.Milnor.vkModelIso w ≠ 0 ∧ e.symm (Work.Milnor.unitOf (Work.Milnor.vkModelIso w)) ∈ Set.range (Submission.Milnor.clutchData (-2)).ιX} := by
  have hlin : ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) ∞
      (fun w : MSpace8 => vkModelIso w) :=
    (ContinuousLinearEquiv.contDiff vkModelIso).contMDiff
  have hunit : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 7) ∞
      (fun w : MSpace8 => unitOf (vkModelIso w))
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    contMDiffOn_unitOf_ne_zero.comp hlin.contMDiffOn (fun w hw => by
      rw [Set.mem_preimage]; exact hw.1)
  have hΦ : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => e.symm (unitOf (vkModelIso w)))
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    (e.symm.contMDiff).comp_contMDiffOn hunit
  have hF : ContMDiffOn 𝓘(ℝ, MSpace8) ((𝓡 4).prod (𝓡 3)) ∞
      (fun w : MSpace8 => (clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w))))
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    (contMDiffOn_clutchHomXsymm (-2)).comp hΦ (fun w hw => by
      rw [Set.mem_preimage, Submission.Glue.Data.homX_target]; exact hw.2)
  have hsndsmooth : ContMDiffOn 𝓘(ℝ, MSpace8) (𝓡 3) ∞
      (fun w : MSpace8 => ((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).2)
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    fun w hw => (hF w hw).snd
  have hcoe' : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun w : MSpace8 =>
        (((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).2 : Quaternion ℝ))
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
    (contMDiff_coe_sphere (E := Quaternion ℝ) (n := 3) (m := ∞)).comp_contMDiffOn hsndsmooth
  have hcoef : ContMDiffOn 𝓘(ℝ, MSpace8) 𝓘(ℝ, ℝ) ∞ (fun w : MSpace8 => ‖vkModelIso w‖⁻¹ + 1/2)
      {w : MSpace8 | vkModelIso w ≠ 0 ∧
        e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} := by
    rw [contMDiffOn_iff_contDiffOn]
    have hnorm : ContDiffOn ℝ ∞ (fun w : MSpace8 => ‖vkModelIso w‖)
        {w : MSpace8 | vkModelIso w ≠ 0 ∧
          e.symm (unitOf (vkModelIso w)) ∈ Set.range (clutchData (-2)).ιX} :=
      ContDiffOn.norm ℝ ((ContinuousLinearEquiv.contDiff vkModelIso).contDiffOn)
        (fun w hw => hw.1)
    exact (hnorm.inv (fun w hw => norm_ne_zero_iff.mpr hw.1)).add contDiffOn_const
  rw [contMDiffOn_prod_module_iff]
  refine ⟨?_, ?_⟩
  · have h1 : (Prod.fst ∘ chartInvFormKX e)
        = (fun w : MSpace8 => ((clutchData (-2)).homX.symm
            (e.symm (unitOf (vkModelIso w)))).1) := rfl
    rw [h1]
    intro w hw
    exact (hF w hw).fst
  · have h2 : (Prod.snd ∘ chartInvFormKX e)
        = (fun w : MSpace8 => (‖vkModelIso w‖⁻¹ + 1/2) •
            (((clutchData (-2)).homX.symm (e.symm (unitOf (vkModelIso w)))).2 : Quaternion ℝ)) := rfl
    rw [h2]
    exact hcoef.smul hcoe'

end

end Work.Milnor
