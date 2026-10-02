/-
# The final assembly: `mandelbar_not_path_connected` modulo `FinalInputs`

Area `Submission/Work/Final/`.  This module contains the **final wiring** of the paper's theorem

  `theorem mandelbar_not_path_connected : ¬ IsPathConnected Mandelbar`

following `Submission/Work/NOTES_LEAD_mandelbar_arc_top.md` §2 and, for the correction of the two
residuals and of the root data, `Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §0 and §4.

## The chain

```
Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch      (DELIVERED, unconditional)
   ← hwin, hθ, hq, hreal, hp, hLB, hX at c₀ on the root arc of the period-5 component H
   ← hwin      : Work.Landing.Angle.window_separation               (DELIVERED)
     hθ        : Work.Final.notMem_closure_top_paramRay_windowAngle  ← Landing + Goldberg–Milnor
     hq, hreal : Work.Final.quarter_mem_closure_paramRay_zero,
                 notMem_closure_paramRay_zero_of_im_ne_zero          (DELIVERED, via paramRay_zero)
     hp        : Work.Final.exists_limitPoint_windowAngle            ← Work.FSeed.exists_paramRay_limit
     hLB       : the field `noPath` of `FinalInputs`, used verbatim  ← PARIMPL (§1)
     hX        : Work.Final.hX_of_twoSided                           ← the field `twoSided`
   ← the *residuals* of §2.3, recorded as fields of `FinalInputs`:
     `noPath` (the **path** form `hLB`: a path in `Mb` cannot approach `c₀` through `Nm`),
     `twoSided` (GATE) — Implosion + EL + the Landing angle lemma;
   ← the root data, as the single export of the `FQC` area
     `Work.FinalFix.RootArcHeightZero = ∃ c₀, ∃ A : RootArc c₀, A.critHeight = 0`
     (§4, row `c₀`/`arc`/`critHeight_zero`); `nonreal` is **derived** from it
     (`Work.FinalFix.nonreal_c₀Of`);
   ← the remaining fields: `Nm`/`impl` (PARIMPL), `nakane` (NAKANE), `gm`/`repAngle`/
     `repAngle_quarter` (LANDCL).
```

Every field of `FinalInputs` is a *named, sorry-free hypothesis*; the assembly below is a complete
proof, so `Submission.mandelbar_not_path_connected_of_inputs` is machine-checked modulo exactly
those fields.  See `Submission/Work/Final/NOTES.md` for the field-by-field provenance.

## What changed with respect to the first version of this area

* `noApproach` (the *set* form `c₀ ∉ closure (Mb ∩ Nm)`) is **dropped**: it is not what the §2.3
  argument proves and it is very likely false (`NOTES_LEAD_mandelbar_residuals.md` §0.1).  Its
  place is taken by the **path** form `noPath`, which is what `TopJordan` consumes; it is used
  directly, without any conversion lemma.
* `nonreal`, `critHeight_zero` and `leak` are **no longer fields**: the first is derived
  (`Work.FinalFix.nonreal`), the second is part of the `root` export, and `leak` is an input of
  the PARIMPL/GATE derivations of `noPath`/`twoSided`, not of the final assembly.

## Main results

* `Work.Final.FinalInputs` — the holder structure;
* `Work.Final.mandelbar_not_path_connected_of_inputs` — the theorem;
* `Work.Final.FinalInputs.nonreal`, `critHeight_zero`, `c₀_mem_Mandelbar`, `exists_escaping_near`,
  `exists_noPer5_near`, `bifSide_of_implSide` — API and non-vacuity.
-/
import Submission.Work.Final.Defs
import Submission.Work.Final.RootArc
import Submission.Work.Final.Glue
import Submission.Work.FinalFix.RootExport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The holder structure of the final assembly.**

It collects every not-yet-delivered ingredient of the chain of
`NOTES_LEAD_mandelbar_arc_top.md` §2 at one root-arc parameter `c₀` of the period-`5` component
`H`, together with the two residuals of the glue §2.3.  The fields are grouped by the area that
owns them; see the module docstring and `NOTES.md`.

* **root data**: `root` — the single export of the `FQC` area, `∃ c₀, ∃ A : RootArc c₀,
  A.critHeight = 0` (`Work.FinalFix.RootArcHeightZero`).  The parameter and the arc data are
  recovered as `FinalInputs.c₀` and `FinalInputs.arc`; the critical Écalle height vanishes by
  construction (`FinalInputs.critHeight_zero`) and `nonreal` is *derived*
  (`FinalInputs.nonreal`);
* **the two residuals of §2.3**: `Nm`, `impl`, `noPath` (the **path** form of `hLB`, §1 of the
  residuals note), `twoSided` (`hX`, §2 of the residuals note);
* **classical inputs**: `nakane` (NAKANE), `gm`, `repAngle`, `repAngle_quarter` (LANDCL). -/
structure FinalInputs where
  /-- **FQC's export**: a parameter of the mandelbar with root-arc data of critical Écalle
  height `0` (`NOTES_LEAD_mandelbar_residuals.md` §4, rows `c₀`, `arc`, `critHeight_zero`; owner
  FQC: `FSeed.exists_rootParabolic_at` + `heightShift` + the root-parabolic transport along
  `principal μ`). -/
  root : Work.FinalFix.RootArcHeightZero
  /-- The implosion side of §2.3 (Implosion, PARIMPL). -/
  Nm : Set ℂ
  /-- The structural properties of `Nm`. -/
  impl : ImplosionSide (Work.FinalFix.c₀Of root) ((Work.FinalFix.arcOf root).d.z₁) Nm
  /-- **`hLB`, in path form**: no path in the connectedness locus approaches `c₀` through the
  implosion side `Nm`.  This is *verbatim* the `hLB` consumed by
  `Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`; it is the form in which the
  §2.3 argument (implosion + equator leak, owner PARIMPL) produces it.  The *set* form
  `c₀ ∉ closure (Mb ∩ Nm)` of the first version is not equivalent and is believed to be false
  (`NOTES_LEAD_mandelbar_residuals.md` §0.1: baby tricorns accumulate at `c₀` inside `Nm`). -/
  noPath : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
    Work.FinalFix.c₀Of root ∉ closure (Set.range γ ∩ Nm)
  /-- **`hX`, in the vocabulary of `Work.ParamRays`**: at every scale a straight segment in
  `Nm ∩ ball c₀ r` carries escaping parameters whose external angles lie in the two windows
  (Implosion + EL + the Landing angle lemma, §2.3; owner GATE).  The form consumed by the
  endgame is `Work.Final.hX_of_twoSided`. -/
  twoSided : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball (Work.FinalFix.c₀Of root) r ∧
    ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
    Work.ParamRays.extAngle e₁ ∈ Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
    Work.ParamRays.extAngle e₂ ∈ Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps)
  /-- Nakane's parameter Böttcher coordinate (ParamRays/NAKANE; classical input bundle). -/
  nakane : Work.ParamRays.NakaneInput
  /-- Goldberg–Milnor Lemma B.1 (LANDCL; the `hθ` clause). -/
  gm : Work.FSeed.RepellingRayParamStable
  /-- The window ray `R(23/63)` lands at a repelling periodic point at `c₀` (LANDCL). -/
  repAngle : ParamAngleRepelling (Work.FinalFix.c₀Of root)
  /-- The same at the period-`1` parabolic parameter `1/4` (LANDCL); this is what makes the
  limit point `p` of `hp` different from `1/4`. -/
  repAngle_quarter : ParamAngleRepelling (1 / 4 : ℂ)

namespace FinalInputs

variable (H : FinalInputs)

/-- The root-arc parameter of the assembly: the parameter of FQC's export. -/
noncomputable def c₀ : ℂ := Work.FinalFix.c₀Of H.root

/-- The root-arc data of the assembly: the arc data of FQC's export. -/
noncomputable def arc : RootArc H.c₀ := Work.FinalFix.arcOf H.root

/-- The critical Écalle height vanishes at the exported parameter: this is part of the `FQC`
export, not an extra hypothesis. -/
theorem critHeight_zero : H.arc.critHeight = 0 := Work.FinalFix.critHeight_arcOf H.root

/-- **`c₀` is non-real** — now *derived* from the root-parabolic structure of the exported arc
(`Work.FinalFix.nonreal`, `Submission/Work/FinalFix/Nonreal.lean`), where the first version of
this area carried it as a hypothesis owned by FSeed
(`NOTES_LEAD_mandelbar_residuals.md` §0.6, §4 row `nonreal`). -/
theorem nonreal : H.c₀.im ≠ 0 := Work.FinalFix.nonreal_c₀Of H.root

/-- The Nakane data of the parameter plane, from the classical input bundle. -/
noncomputable def nakaneData : Work.Top.NakaneData Mandelbar Work.ParamRays.Phi :=
  Work.ParamRaysCrit.nakaneData H.nakane

/-- The root-arc parameter is a parameter of the mandelbar. -/
theorem c₀_mem_Mandelbar : H.c₀ ∈ Mandelbar := H.arc.mem_Mandelbar

/-- `c₀` is not the period-`1` parabolic parameter `1/4` (it is non-real). -/
theorem c₀_ne_quarter : H.c₀ ≠ (1 / 4 : ℂ) := by
  intro h
  exact H.nonreal (by rw [h]; simp)

/-- **FBif is implied by the implosion side** (see `Work.Final.ImplosionSide.toBifSide`): the
bifurcation side holds at `c₀`, i.e. arbitrarily close to `c₀` there are parameters with no
period-`5` point near the parabolic point.  This is the non-vacuity certificate of the hypotheses
`noPath`/`twoSided`. -/
theorem bifSide_of_implSide : BifSide H.c₀ H.arc.d.z₁ := H.impl.toBifSide

/-- The implosion side is nonempty (it accumulates at `c₀`). -/
theorem Nm_nonempty : H.Nm.Nonempty := H.impl.nonempty

/-- Non-vacuity of `twoSided`: at every scale there is an *escaping* parameter in
`ball c₀ r` (indeed in the segment produced by `twoSided`). -/
theorem exists_escaping_near (r : ℝ) (hr : 0 < r) :
    ∃ c ∈ Metric.ball H.c₀ r, c ∉ Mandelbar := by
  obtain ⟨x, y, hseg, e₁, he₁, e₂, he₂, h₁, h₂, -, -⟩ := H.twoSided r hr
  exact ⟨e₁, (hseg he₁).2, h₁⟩

/-- Non-vacuity of the bifurcation side: at every scale there is a parameter in `ball c₀ r` at
which the period-`5` orbit near `z₁` has disappeared. -/
theorem exists_noPer5_near (r : ℝ) (hr : 0 < r) :
    ∃ δ > 0, ∃ c ∈ Metric.ball H.c₀ r,
      ∀ z ∈ Metric.ball H.arc.d.z₁ δ, (Tantibar c)^[5] z ≠ z := by
  obtain ⟨δ, hδ, h⟩ := H.bifSide_of_implSide
  exact ⟨δ, hδ, h r hr⟩

/-- **The endgame hypotheses hold at `c₀`.**  The `hLB` slot is filled by the field `noPath`
itself (no conversion), and `hq` is the derived `nonreal`. -/
theorem endgame_hypotheses :
    (0 < alpha1 - windowEps ∧ alpha1 + windowEps < windowAngle ∧
      windowAngle < alpha2 - windowEps ∧ alpha2 + windowEps < 1) ∧
    (H.c₀ ∉ closure (Work.Top.NakaneData.paramRay (nakaneData H) windowAngle)) ∧
    (H.c₀ ≠ (1 / 4 : ℂ)) ∧
    ((1 / 4 : ℂ) ∈ Mandelbar ∧
      (1 / 4 : ℂ) ∈ closure (Work.Top.NakaneData.paramRay (nakaneData H) 0) ∧
      H.c₀ ∉ closure (Work.Top.NakaneData.paramRay (nakaneData H) 0)) ∧
    (∃ p : ℂ, p ∈ Mandelbar ∧
      p ∈ closure (Work.Top.NakaneData.paramRay (nakaneData H) windowAngle) ∧
      (p ≠ (1 / 4 : ℂ) ∧ p ∉ Work.Top.NakaneData.paramRay (nakaneData H) windowAngle)) ∧
    (∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
      H.c₀ ∉ closure (Set.range γ ∩ H.Nm)) ∧
    (∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ H.Nm ∩ Metric.ball H.c₀ r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.Top.NakaneData.extAngle Work.ParamRays.Phi e₁ ∈
        Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
      Work.Top.NakaneData.extAngle Work.ParamRays.Phi e₂ ∈
        Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps)) :=
  ⟨window_separation,
    notMem_closure_top_paramRay_windowAngle (nakaneData H) H.gm H.repAngle,
    c₀_ne_quarter H,
    ⟨Work.ParamRays.quarter_mem,
      by rw [top_paramRay_eq (nakaneData H) 0]; exact quarter_mem_closure_paramRay_zero H.nakane,
      by rw [top_paramRay_eq (nakaneData H) 0]
         exact notMem_closure_paramRay_zero_of_im_ne_zero H.nakane H.nonreal⟩,
    exists_limitPoint_windowAngle (nakaneData H) H.gm H.repAngle_quarter,
    H.noPath,
    hX_of_twoSided H.twoSided⟩

end FinalInputs

/-- **The endgame, assembled.**  If the holder structure `FinalInputs` holds, then the mandelbar
is not path-connected: this is the final wiring of
`Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch` with the delivered glue
(`window_separation`, `hθ`, `hreal`, `hp`, and the conversion of `hX`) and the residuals of
`NOTES_LEAD_mandelbar_arc_top.md` §2.3 at one root-arc parameter `c₀`. -/
theorem mandelbar_not_path_connected_of_inputs (H : FinalInputs) :
    ¬ IsPathConnected Mandelbar := by
  obtain ⟨hwin, hθ, hq, hreal, ⟨p, hpMb, hpcl, hpq, -⟩, hLB, hX⟩ := H.endgame_hypotheses
  exact Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch
    Work.ParamRays.Phi (H.nakaneData) H.c₀ H.Nm alpha1 alpha2 windowAngle windowEps
    hwin hθ hq hreal ⟨p, hpMb, hpcl, hpq⟩ hLB hX

/-- **The unbundled form of the final theorem**, for callers that do not want the holder
structure: the same statement with the fields of `FinalInputs` as explicit hypotheses (note that
`nonreal`, `critHeight_zero` and `leak` do not occur: the first two come with `root`, the last is
not part of the assembly). -/
theorem mandelbar_not_path_connected_of_data
    (root : Work.FinalFix.RootArcHeightZero)
    (Nm : Set ℂ)
    (impl : ImplosionSide (Work.FinalFix.c₀Of root) ((Work.FinalFix.arcOf root).d.z₁) Nm)
    (noPath : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mandelbar) →
      Work.FinalFix.c₀Of root ∉ closure (Set.range γ ∩ Nm))
    (twoSided : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball (Work.FinalFix.c₀Of root) r ∧
      ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mandelbar ∧ e₂ ∉ Mandelbar ∧
      Work.ParamRays.extAngle e₁ ∈ Set.Ioo (alpha1 - windowEps) (alpha1 + windowEps) ∧
      Work.ParamRays.extAngle e₂ ∈ Set.Ioo (alpha2 - windowEps) (alpha2 + windowEps))
    (nakane : Work.ParamRays.NakaneInput) (gm : Work.FSeed.RepellingRayParamStable)
    (repAngle : ParamAngleRepelling (Work.FinalFix.c₀Of root))
    (repAngle_quarter : ParamAngleRepelling (1 / 4 : ℂ)) :
    ¬ IsPathConnected Mandelbar :=
  mandelbar_not_path_connected_of_inputs
    ⟨root, Nm, impl, noPath, twoSided, nakane, gm, repAngle, repAngle_quarter⟩

end Work.Final
