/-
# `Work.NAKANE` — Nakane's parameter Böttcher map: joint continuity and the exterior

Area owner: the NAKANE agent.  Requested by the lead (`Submission/Work/NOTES_LEAD_mandelbar_residuals.md`
§0/§4, row `nakane`): *"Deliver `NakaneHomeo` (Φ continuous and a homeomorphism onto the exterior,
via joint (c,z)-continuity of the Green function and of the critical Böttcher coordinate) and
`UniformBottcherAsymptotic` (φ_c(c)/c → 1 uniformly), in the forms `FinalInputs` uses, plus the
joint Green/Böttcher continuity lemmas PARIMPL and GATE need."*

This file fixes the vocabulary of the area.

## The two continuities

* `Work.NAKANE.jointGreen : ℂ × ℂ → ℝ`, `p ↦ G_{p.1} p.2` — the Green function as a function of
  (parameter, point).  `continuous_jointGreen` (module `Work.NAKANE.GreenJoint`) is its joint
  continuity; this is the input of PARIMPL's (I2).
* `Work.NAKANE.jointVarphi : ℂ × ℂ → ℂ`, `p ↦ φ_{p.1} p.2` — the canonical critical Böttcher
  coordinate as a function of (parameter, point).
  `continuousOn_jointVarphi` (module `Work.NAKANE.BottcherJoint`) is its joint continuity on
  `jointDomain = {(c,z) | z ∈ critDomain c}`; this is the input of GATE.

## The parameter Böttcher map and its two residuals

`Work.ParamRays.Phi c = φ_c(c) = Φ c` is the parameter Böttcher map (junk value `0` on the
mandelbar).  It is the *critical value* of the joint Böttcher coordinate, so the joint continuity
above gives `ContinuousOn Phi Mbᶜ` and `Continuous (potential Mb Phi)` **unconditionally**
(`Work.NAKANE.PhiContinuity`).

`NakaneHomeo` is the classical statement that `Φ` is a homeomorphism onto `{w | 1 < ‖w‖}`.  The
area proves everything about `Φ` that does *not* require holomorphy in the parameter:

* `Phi_proper`, `Phi_isClosedMap`, `tendsto_Phi_atTop` (module `Work.NAKANE.PhiProper`):
  `‖Φ c‖ = exp (2 G_c(0))` makes `Φ` proper and closed, and `Φ c / c → 1`;
* `uniformBottcherAsymptotic` (module `Work.NAKANE.Asymptotic`):
  `Work.ParamRays.UniformBottcherAsymptotic`;
* `Phi_surjective_of_localHomeo` (module `Work.NAKANE.NakaneHomeo`): proper + open ⟹ the image of
  `Mbᶜ` is open and closed in the (preconnected) exterior, hence is the whole exterior;
* `nakaneHomeo_of_localHomeo_of_injOn` (module `Work.NAKANE.NakaneHomeo`): the assembly of
  `NakaneHomeo` from the two classical inputs `PhiLocalHomeo` and `PhiInjOn`.

The two inputs are recorded as named propositions here, so that their content is visible in one
place; both are *true* statements of the classical theory (Nakane 1993): `c ↦ Φ c` is
real-analytic with nonvanishing Jacobian on `Mbᶜ` (whence `PhiLocalHomeo`), and `Φ` is injective on
`Mbᶜ`.  Neither is proved in this workspace.
-/
import Submission.Work.ParamRaysCrit.All
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Bottcher.Inverse.eq_bottcher_of_analytic_far
import Submission.Work.Bottcher.Core.bottcher_comm_pMap
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop

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

/-! ## The mandelbar and its exterior -/

/-- The mandelbar (the connectedness locus), as used everywhere in the project. -/
abbrev Mb : Set ℂ := Mandelbar

/-- The exterior of the closed unit disc: the target of Nakane's parameter Böttcher map. -/
abbrev extDisc : Set ℂ := {w : ℂ | 1 < ‖w‖}

/-! ## The joint Green function -/

/-- The Green function of the tricorn family, as a function of the pair `(c, z)`. -/
def jointGreen (p : ℂ × ℂ) : ℝ := Work.Escape.green (Tantibar p.1) 2 p.2

theorem jointGreen_apply (c z : ℂ) :
    jointGreen (c, z) = Work.Escape.green (Tantibar c) 2 z := rfl

/-- The critical domain of the pair `(c,z)`: `z ∈ critDomain c = {G_c > G_c 0}`. -/
def jointDomain : Set (ℂ × ℂ) := {p | p.2 ∈ Work.ParamRays.critDomain p.1}

theorem mem_jointDomain {p : ℂ × ℂ} :
    p ∈ jointDomain ↔ p.2 ∈ Work.ParamRays.critDomain p.1 := Iff.rfl

/-- A radius beyond which the point `z` certainly lies in the critical domain `critDomain c` and
in the far region of the product formula: `2 (1 + C)^2 + 2`.  For `‖c‖ ≤ C` the ball
`{‖z‖ > farRadius C}` is contained in `critDomain c` (`mem_critDomain_of_farRadius_lt`) and in
`{escapeRadius c < ‖z‖}`; on it the explicit product formula is the canonical Böttcher coordinate
(`jointVarphi_eq_jointBottcher_of_far`).

It is deliberately *not* the sharp escape radius: the sharp inclusion
`{escapeRadius c < ‖z‖} ⊆ critDomain c` is not available in the workspace, whereas the coarse
radius above is easily dominated by the two Green-function bounds
`Work.Escape.log_half_le_green` (`G_c z ≥ log (‖z‖/2)` for `max 2 ‖c‖ < ‖z‖`) and
`Work.Escape.green_le_log` (`G_c 0 ≤ 2 log (max 2 (‖c‖+1))`): for `‖c‖ ≤ C` and
`‖z‖ > farRadius C` one has `‖z‖/2 > (max 2 (1+‖c‖))^2`, hence
`G_c 0 ≤ 2 log (max 2 (1+‖c‖)) < log (‖z‖/2) ≤ G_c z`. -/
noncomputable def farRadius (C : ℝ) : ℝ := 2 * (max 2 (1 + C)) ^ 2 + 2

/-- The "far block" `‖c‖ ≤ C`, `R ≤ ‖z‖` in the (parameter, point) plane.  On it the critical
Böttcher coordinate is given by the explicit product formula of `Work.Bottcher`. -/
def farBlock (C R : ℝ) : Set (ℂ × ℂ) := {p | ‖p.1‖ ≤ C ∧ R < ‖p.2‖}

theorem pos_farRadius (C : ℝ) : 0 < farRadius C := by
  unfold farRadius
  positivity

theorem mem_farBlock {C R : ℝ} {p : ℂ × ℂ} :
    p ∈ farBlock C R ↔ ‖p.1‖ ≤ C ∧ R < ‖p.2‖ := Iff.rfl

/-! ## The joint critical Böttcher coordinate -/

/-- The canonical critical Böttcher coordinate of `T_c`, as a function of the pair `(c, z)`. -/
def jointVarphi (p : ℂ × ℂ) : ℂ := Work.Bottcher.varphiCrit p.1 p.2

theorem jointVarphi_apply (c z : ℂ) : jointVarphi (c, z) = Work.Bottcher.varphiCrit c z := rfl

/-- The explicit product formula of `Work.Bottcher`, as a function of `(c, z)`. -/
def jointBottcher (p : ℂ × ℂ) : ℂ := Work.Bottcher.bottcher p.1 p.2

theorem jointBottcher_apply (c z : ℂ) : jointBottcher (c, z) = Work.Bottcher.bottcher c z := rfl

/-! ## The parameter Böttcher map -/

/-- The parameter Böttcher map `Φ c = φ_c(c)`. -/
def Phi (c : ℂ) : ℂ := Work.ParamRays.Phi c

theorem Phi_eq_ParamRays (c : ℂ) : Phi c = Work.ParamRays.Phi c := rfl

/-- The parameter potential `c ↦ G_c(0)` (the Green function at the critical point). -/
def potential (c : ℂ) : ℝ := Work.ParamRays.paramPotential c

/-! ## The two classical residual inputs of `NakaneHomeo` -/

/-- **(R1) `Φ` is a local homeomorphism on the exterior of the mandelbar.**  This is the classical
regularity of the parameter Böttcher map (Nakane 1993, following Douady–Hubbard): `c ↦ Φ c` is
real-analytic with nonvanishing Jacobian on `Mbᶜ`.  It is taken as a named hypothesis here; what
this area proves from it is `Phi_surjective_of_localHomeo` and (with (R2))
`nakaneHomeo_of_localHomeo_of_injOn`. -/
def PhiLocalHomeo : Prop := IsLocalHomeomorphOn Phi Mbᶜ

/-- **(R2) `Φ` is injective on the exterior of the mandelbar.**  This is the other half of
Nakane's theorem. -/
def PhiInjOn : Prop := InjOn Phi Mbᶜ

end Work.NAKANE
