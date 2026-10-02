/-
# Continuity of the parameter Böttcher map `Φ` and of the parameter potential

`Work.ParamRays.Phi c = φ_c(c)` is the parameter Böttcher map of Nakane (junk value `0` on the
mandelbar).  The joint continuity of `(c,z) ↦ φ_c(z)` (`Work.NAKANE.BottcherJoint`) gives, with no
further input:

* `Work.NAKANE.Phi_eq_varphiCrit` : `Φ c = φ_c(c)` off the mandelbar;
* `Work.NAKANE.continuousOn_Phi` : `Φ` is continuous on `Mbᶜ` — **unconditionally** (the existing
  `Work.ParamRays.continuousOn_Phi_compl` takes `NakaneInput` as a hypothesis);
* `Work.NAKANE.potential_eq_two_paramPotential` and `Work.NAKANE.continuous_potential` : the
  parameter potential is `2 * G_c(0)` and is **continuous on the whole plane**, unconditionally
  (again the existing `Work.ParamRays.continuous_potential` takes `NakaneInput`).

These discharge two of the five fields of `Work.Top.NakaneData` at `Φ = Work.ParamRays.Phi`
(continuity of the potential, and — via the joint continuity — the agreement of `Φ` with a
*continuous* map on `Mbᶜ`).
-/
import Submission.Work.NAKANE.BottcherJoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- Off the mandelbar the parameter Böttcher map is the critical Böttcher coordinate at the
critical value. -/
theorem Phi_eq_varphiCrit {c : ℂ} (hc : c ∉ Mb) :
    Work.ParamRays.Phi c = Work.Bottcher.varphiCrit c c :=
  calc Work.ParamRays.Phi c = Work.Bottcher.PhiCrit c := (Work.Bottcher.PhiCrit_eq_Phi c).symm
    _ = Work.Bottcher.varphiCrit c c :=
        Work.Bottcher.PhiCrit_eq_of_isCritBottcher hc (Work.Bottcher.isCritBottcher_varphiCrit c)

/-- **`Φ` is continuous on the exterior of the mandelbar**, unconditionally. -/
theorem continuousOn_Phi : ContinuousOn Work.ParamRays.Phi {c : ℂ | c ∉ Mb} :=
  continuousOn_varphiCrit_self.congr fun c hc => Phi_eq_varphiCrit hc

/-- **The parameter potential is twice the Green function of the critical point.** -/
theorem potential_eq_two_paramPotential (c : ℂ) :
    Work.ParamRays.potential c = 2 * Work.ParamRays.paramPotential c := by
  by_cases hc : c ∈ Mb
  · have h0 : Work.ParamRays.paramPotential c = 0 :=
      (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hc
    rw [Work.ParamRays.potential_eq_zero_of_mem hc, h0, mul_zero]
  · rw [Work.ParamRays.potential, dif_neg hc,
      Work.ParamRays.norm_Phi_eq_exp Work.Bottcher.bottcherExists_crit hc, Real.log_exp]

/-- **The parameter potential is continuous on the whole plane**, unconditionally. -/
theorem continuous_potential : Continuous Work.ParamRays.potential := by
  have h : Work.ParamRays.potential = fun c : ℂ => 2 * Work.ParamRays.paramPotential c :=
    funext potential_eq_two_paramPotential
  rw [h]
  exact continuous_const.mul continuous_paramPotential

end Work.NAKANE
