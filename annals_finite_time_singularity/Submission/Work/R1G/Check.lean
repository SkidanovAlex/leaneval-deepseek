/-
# `Work.R1G.Check` — the `hR1`-free end-to-end check of the G-route

Deliverable 3 of the G-route: the end-to-end check of `Work.CoreResiduals.Check` with residual **R1**
replaced by its *honest* (deficit) form.  The chain is

  `GResiduals α P Def`  →`Def = 0`→  `CoreResiduals α P`  →  `ConstructedSolutionFixed α`
      →  `Work.SolutionDelivery.Theorem1Statement`,

and the mechanical step is `Work.CoreResiduals.vortEq_iff_noDeficit`
(`VortEq α P ↔ VortEqWithDeficit P 0`): the deficit form at zero deficit *is* the delivered residual.
So the whole file compiles against the delivered residual interface and the lead's
`Submission.lean` wiring is unchanged — what changes is the *interface field*: the G-route's owner
supplies `VortEqWithDeficit P Def` (with the deficit carried explicitly) instead of the (false)
zero-deficit statement.

## What "the `hR1`-free check" means here, precisely

* `Work.R1G.GResiduals` — the residual interface with the deficit form of R1 in place of `vortEq`;
* `Work.R1G.coreResiduals_of_gResiduals_zero` — the deficit form at `Def = 0` *is*
  `Work.ConstructionInstance.CoreResiduals`;
* `Work.R1G.theorem1_of_gResiduals` — the end-to-end check from `GResiduals α P 0`;
* `Work.R1G.theorem1_of_honestR1` — the same from the deficit form plus the *vanishing* of the
  deficit (the "deficit cancellation" of the G-route, `Work.R1G.vortEq_of_honestR1_of_deficit_eq_zero`);
* `Work.R1G.GRouteHyp` — the honest hypothesis: a `ModulatedData` (`g ≠ 0` solving the
  `St2`/`St3` `g`-equation with vanishing far-field term), the ansatz dictionary, and the
  **profile-level deficit cancellation** `χ(ρP/L)·meridianResid W Ψ = -cutDeficit P Ψ W`; with
  `Work.R1G.meridianResid_eq_zero_of_gRoute`, `Work.R1G.vortEq_of_gRoute` and
  `Work.R1G.theorem1_of_gRoute`;
* **`Work.R1G.theorem1_of_model_data_deficitForm`** — `Work.CoreResiduals.theorem1_of_model_data`
  **with `hR1` closed** by the deficit form;
* **`Work.R1G.check_theorem_1_of_inputs_of_fixed_deficitForm`** — the *verbatim* wiring of
  `Work.SolutionDelivery.check_theorem_1_of_inputs` / `Work.StabilityFar.theorem_1_of_inputs` at the
  same data;
* **`Work.R1G.theorem1_of_modulated_data`** — at the modulated data, with R2/R3 as theorems.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.R1G.Defs
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.MeridianDeficit
import Submission.Work.CoreResiduals.Check

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

variable {α : NNReal}

/-! ## The residual interface with the deficit form of R1 -/

/-- **The G-route residual interface**: the delivered minimal residual interface
(`Work.ConstructionInstance.CoreResiduals`) with the zero-deficit field `vortEq` replaced by the
*deficit* form `Work.CoreResiduals.VortEqWithDeficit P Def`.  At `Def = 0` this is the delivered
interface (`Work.R1G.coreResiduals_of_gResiduals_zero`), so the G-route is *strictly* an interface
change for R1 and nothing else. -/
structure GResiduals (α : NNReal) (P : Work.ConstructionInstance.ProfileData α)
    (Def : R3 → ℝ → R3) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- **R1 in deficit form**: the `ℝ³` vorticity equation up to the explicit deficit `Def` -/
  vortEqDef : Work.CoreResiduals.VortEqWithDeficit P Def
  /-- **R2** -/
  lgClass : Work.CoreResiduals.LGClass α P
  /-- **R3** -/
  smooth : Work.CoreResiduals.VortSmooth P
  /-- **R4** -/
  timeHolderDeriv : Work.CoreResiduals.TimeHolderDeriv P

/-- **The zero-deficit case is the delivered interface**: `GResiduals α P 0` *is*
`Work.ConstructionInstance.CoreResiduals α P` (through
`Work.CoreResiduals.vortEq_iff_noDeficit`). -/
theorem coreResiduals_of_gResiduals_zero {P : Work.ConstructionInstance.ProfileData α}
    (T : GResiduals α P (fun _ _ => 0)) : Work.ConstructionInstance.CoreResiduals α P :=
  { lwp := T.lwp
    vortEq := (Work.CoreResiduals.vortEq_iff_noDeficit P).mpr T.vortEqDef
    lgClass := T.lgClass
    smooth := T.smooth
    timeHolderDeriv := T.timeHolderDeriv }

/-- **THE `hR1`-FREE END-TO-END CHECK (deficit form at zero deficit).**  From `GResiduals α P 0`
— the deficit-form interface with vanishing deficit — and the patched consumer, the challenge
statement follows.  Mechanically this is `Work.CoreResiduals.theorem1_of_residuals` after the
rewrite `Work.R1G.coreResiduals_of_gResiduals_zero`. -/
theorem theorem1_of_gResiduals (consumer : Work.CoreResiduals.PatchedConsumer) {P : _root_.Work.ConstructionInstance.ProfileData α}
    (T : GResiduals α P (fun _ _ => 0)) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.CoreResiduals.theorem1_of_residuals consumer (coreResiduals_of_gResiduals_zero T) hα hα1

/-- **The deficit cancellation as a step.**  If the deficit form holds and the deficit vanishes
identically, then the *delivered* residual R1 holds — and hence the whole `CoreResiduals` interface
can be assembled from the deficit form. -/
theorem vortEq_of_deficit_eq_zero {P : Work.ConstructionInstance.ProfileData α}
    {Def : R3 → ℝ → R3} (h : Work.CoreResiduals.VortEqWithDeficit P Def)
    (h0 : ∀ x t, Def x t = 0) : Work.CoreResiduals.VortEq α P := by
  rw [Work.CoreResiduals.vortEq_iff_noDeficit]
  intro x t
  rw [h x t, h0 x t]

/-- **The `hR1`-free check from the honest residual.**  The G-route's honest residual hypothesis is
`HonestR1 P Far` (the deficit form with the *explicit*, profile-level deficit `fieldImage P Far`)
together with the vanishing of `Far`; the conclusion is the delivered R1, hence the challenge
statement. -/
theorem theorem1_of_honestR1 (consumer : Work.CoreResiduals.PatchedConsumer)
    {P : Work.ConstructionInstance.ProfileData α} {Far : ℝ → ℝ → ℝ}
    (hlwp : Work.LWP.LWPInputs α) (h : HonestR1 P Far) (h0 : ∀ z θ : ℝ, Far z θ = 0)
    (hG : Work.CoreResiduals.LGClass α P) (hsm : Work.CoreResiduals.VortSmooth P)
    (hth : Work.CoreResiduals.TimeHolderDeriv P)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.CoreResiduals.theorem1_of_four consumer hlwp
    (vortEq_of_honestR1_of_deficit_eq_zero P h h0) hG hsm hth hα hα1

/-! ## The honest G-route hypothesis -/

/-- **The G-route's honest hypothesis for R1.**  The modulated profile data (`g ≠ 0` solving the
`St2`/`St3` `g`-equation with vanishing far-field term), the two halves of the ansatz dictionary
(the constructed velocity is the stream-function field of `Ψ`; the constructed vorticity is the cut
meridian profile `χ(ρ/L)·W`), and the **deficit cancellation at the profile level**:

  `χ(ρP(r,z)/L)·meridianResid W Ψ = -cutDeficit P Ψ W`.

By the cut-off identity (`Work.R1G.meridianResid_cut`) this is *exactly* the vanishing of the
meridian residual of the constructed field, hence — through the field/meridian bridge
(`Work.R1G.vortEqWithDeficit_iff_meridian_field`) — exactly the delivered residual R1.  Its content
is the *decomposition*: the profile-level statement (what the `g`-equation controls, through
`Work.R1G.ProfileEq`) plus the **explicit** cut-off term `cutDeficit` (fixed by the `St1` bump).

Note that this hypothesis *cannot* hold with the self-similar stream function `ssPsiOf` (there the
uncut residual vanishes by the profile equation, so the cancellation would force `cutDeficit = 0`);
it holds for the *actual* stream function of the constructed field, which is the elliptic
identification — see `NOTES.md` §5. -/
structure GRouteHyp (α : NNReal) where
  /-- the modulated profile data (`g ≠ 0` solving the `g`-equation) -/
  D : ModulatedData α
  /-- the `g`-equation's far-field term vanishes -/
  hFar : ∀ z θ : ℝ, D.Far z θ = 0
  /-- the meridian stream function of the constructed velocity -/
  Ψ : ℝ → ℝ → ℝ → ℝ
  /-- the meridian profile of the *uncut* constructed vorticity -/
  W : ℝ → ℝ → ℝ → ℝ
  /-- the ansatz dictionary: the velocity is the stream-function field of `Ψ` -/
  hv : ∀ x t, Work.ConstructionInstance.ansatzV D.P x t = Work.Cyl.cylField
    (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
    (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x
  /-- the ansatz dictionary: the vorticity is the cut meridian profile -/
  hω : ∀ x t, Work.ConstructionInstance.solVort D.P x t
    = cutProfile D.P W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x
  /-- the stream function is `C²` in the meridian variables -/
  hΨ : ∀ t r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2 t) (r, z)
  /-- the uncut meridian profile is differentiable along `r` -/
  hWr : ∀ t r z : ℝ, 0 < r → DifferentiableAt ℝ (fun r' : ℝ => W r' z t) r
  /-- the uncut meridian profile is differentiable along `z` -/
  hWz : ∀ t r z : ℝ, 0 < r → DifferentiableAt ℝ (fun z' : ℝ => W r z' t) z
  /-- the uncut meridian profile is differentiable in `t` -/
  hWt : ∀ t r z : ℝ, 0 < r → DifferentiableAt ℝ (fun s : ℝ => W r z s) t
  /-- the cut meridian profile is differentiable in the meridian variables -/
  hWc : ∀ t r z : ℝ, 0 < r →
    Work.Cyl.DiffAt2 (fun r z => cutProfile D.P W r z t) r z
  /-- **the deficit cancellation**: the profile-level residual cancels the explicit cut-off term -/
  hcancel : ∀ r z t : ℝ, 0 < r →
    Work.Stability.chi (Work.Cyl.rhoP r z / D.P.L)
        * Work.CoreResiduals.meridianResid W Ψ r z t
      = - cutDeficit D.P Ψ W r z t

/-- From the G-route's hypothesis, the meridian residual of the constructed field vanishes. -/
theorem meridianResid_eq_zero_of_gRoute (G : GRouteHyp α) :
    ∀ r z t : ℝ, 0 < r →
      Work.CoreResiduals.meridianResid (cutProfile G.D.P G.W) G.Ψ r z t = 0 :=
  fun r z t hr => meridianResid_cutProfile_eq_zero_of_cancel G.D.P hr
    (G.hWr t r z hr) (G.hWz t r z hr) (G.hWt t r z hr) (G.hcancel r z t hr)

/-- **The G-route's hypothesis gives the delivered residual R1.**  The dictionary plus the
profile-level cancellation of the explicit cut-off term is exactly the `ℝ³` vorticity equation for
the constructed field. -/
theorem vortEq_of_gRoute (G : GRouteHyp α) : Work.CoreResiduals.VortEq α G.D.P := by
  rw [Work.CoreResiduals.vortEq_iff_noDeficit]
  rw [show (fun x t => (0 : R3))
      = (fun x t => (fun _ _ _ => (0 : ℝ)) (Work.Cyl.radial x) (Work.Cyl.axial x) t
          • Work.Cyl.eTheta x) from by funext x t; simp]
  exact (vortEqWithDeficit_iff_meridian_field G.D.P G.hv G.hω G.hΨ G.hWc
    (WD := fun _ _ _ => (0 : ℝ))).mpr (meridianResid_eq_zero_of_gRoute G)

/-- **THE `hR1`-FREE CHECK.**  The challenge statement follows from the G-route's honest data
(`GRouteHyp α`) together with the LWP inputs, R2, R3 and R4 supplied by the caller. -/
theorem theorem1_of_gRoute (consumer : Work.CoreResiduals.PatchedConsumer) (G : GRouteHyp α)
    (hlwp : Work.LWP.LWPInputs α) (hG : Work.CoreResiduals.LGClass α G.D.P)
    (hsm : Work.CoreResiduals.VortSmooth G.D.P)
    (hth : Work.CoreResiduals.TimeHolderDeriv G.D.P)
    (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.CoreResiduals.theorem1_of_four consumer hlwp
    (vortEq_of_gRoute G) hG hsm hth hα hα1


/-! ## At the delivered inhabitant: the mechanical rewrite -/

/-- **R1 in deficit form at the delivered inhabitant.**  `Work.CoreResiduals.theorem1_of_model_data`
**with `hR1` closed** by the deficit form: the deficit `Def` is the explicit deficit of the
interface, and when it vanishes identically the delivered residual `VortEq α I.P` holds —
`Work.CoreResiduals.vortEq_iff_noDeficit` makes the substitution definitional, which is exactly the
"mechanical rewrite" of the recommendation. -/
theorem theorem1_of_model_data_deficitForm (consumer : Work.CoreResiduals.PatchedConsumer)
    (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3)
    (I : Work.CoreResiduals.Inhabitant α) (hlwp : Work.LWP.LWPInputs α)
    {Def : R3 → ℝ → R3} (hDef : Work.CoreResiduals.VortEqWithDeficit I.P Def)
    (h0 : ∀ x t, Def x t = 0) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.CoreResiduals.theorem1_of_model_data consumer hα hα13 I hlwp
    (vortEq_of_deficit_eq_zero hDef h0)

/-- **The end-to-end check through the *verbatim* wiring of
`Work.SolutionDelivery.check_theorem_1_of_inputs`**, at the delivered inhabitant and with R1 in
deficit form (so `hR1` is closed as soon as the deficit vanishes).  `assemble` is the patched
`assemblyInputs_of_constructed`, exactly as in the delivered check; R2, R3 and R4 are the theorems
of `Work.CoreResiduals` at the inhabitant. -/
theorem check_theorem_1_of_inputs_of_fixed_deficitForm
    (assemble : ∀ {α : NNReal}, Work.ConstructionInstance.ConstructedSolutionFixed α →
      Work.StabilityFar.AssemblyInputs α)
    {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3)
    (I : Work.CoreResiduals.Inhabitant α) (hlwp : Work.LWP.LWPInputs α)
    {Def : R3 → ℝ → R3} (hDef : Work.CoreResiduals.VortEqWithDeficit I.P Def)
    (h0 : ∀ x t, Def x t = 0)
    (hscl : Work.StabilityFar.EulerScalingToUnit) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.CoreResiduals.check_theorem_1_of_inputs_of_fixed assemble
    { lwp := hlwp
      vortEq := vortEq_of_deficit_eq_zero hDef h0
      lgClass := Work.CoreResiduals.lgClass_of_spaceTime I.P
        (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds hα (by linarith))
        (fun S hS hST => Work.CoreResiduals.solVort_BSAdmissibleStripFull I.P
          (Work.CoreResiduals.timeDerivLocallyLipschitz_of_inhabitant I) hS hST)
      smooth := Work.CoreResiduals.vortSmooth_of_spacetimeC1 I.P
        Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
        (Work.CoreResiduals.solVort_BSAdmissibleOnWindow I.P)
        (Work.CoreResiduals.timeDerivLocallyLipschitz_of_inhabitant I)
      timeHolderDeriv := Work.CoreResiduals.timeHolderDeriv_of_inhabitant I }
    hα (by linarith) hscl

/-! ## At the modulated data: R1 by the G-route, R2/R3 as theorems

The honest (modulated) data is a *different* `ProfileData` from the delivered inhabitant (`g ≠ 0`
versus `g = 0`), so R2/R3/R4 must be read at *its* field `solVort G.D.P`.  The two analytic inputs
of `Work.CoreResiduals` (`biotSavartSpaceTime_holds`, `biotSavartSpacetimeC1_holds`) and the two
bundles are proved for the *general* `ProfileData` (`solVort_BSAdmissibleStripFull`,
`solVort_BSAdmissibleOnWindow`), so **R2 and R3 are theorems at the modulated data as well**, the
only extra input being the second-order joint-`C¹` condition
`TimeDerivLocallyLipschitz (solVort G.D.P) G.D.P.T`; R4 (finding H) remains the caller's.  This is
the honest form of `Work.CoreResiduals.theorem1_of_model_data` with `hR1` closed by the G-route. -/
theorem theorem1_of_modulated_data (consumer : Work.CoreResiduals.PatchedConsumer)
    (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3)
    (hlwp : Work.LWP.LWPInputs α) (G : GRouteHyp α)
    (hlip : Work.CoreResiduals.TimeDerivLocallyLipschitz
      (Work.ConstructionInstance.solVort G.D.P) G.D.P.T)
    (hth : Work.CoreResiduals.TimeHolderDeriv G.D.P) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.CoreResiduals.theorem1_of_four consumer hlwp (vortEq_of_gRoute G)
    (Work.CoreResiduals.lgClass_of_spaceTime G.D.P
      (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds hα (by linarith))
      (fun S hS hST => Work.CoreResiduals.solVort_BSAdmissibleStripFull G.D.P hlip hS hST))
    (Work.CoreResiduals.vortSmooth_of_spacetimeC1 G.D.P
      Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
      (Work.CoreResiduals.solVort_BSAdmissibleOnWindow G.D.P) hlip)
    hth hα (by linarith)

end Work.R1G
