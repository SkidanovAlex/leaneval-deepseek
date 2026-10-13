/-
# `Work.CoreResiduals.Check` — the end-to-end check

This is the module the lead wires `Submission.lean` to.  It provides:

* `constructedSolutionFixed_of_residuals` — the minimal residual interface
  `Work.ConstructionInstance.CoreResiduals α P` produces the repaired input package
  `Work.ConstructionInstance.ConstructedSolutionFixed α`;
* `theorem1_of_residuals` — the challenge statement (`Work.SolutionDelivery.Theorem1Statement`)
  from that interface alone, with the **patched consumer** `consumer` (the delivered
  `Work.SolutionDelivery.theorem_1_of_constructed` with `ConstructedSolution` replaced by
  `ConstructedSolutionFixed`, the interface patch of `NOTES.md` §5 item 1) as an explicit
  argument, so that this module compiles before the patch is applied and is the literal call
  `consumer (constructedSolutionFixed_of_residuals T)` afterwards;
* `theorem1_of_four` — the same, taking the **four named residuals separately** plus the LWP
  inputs (the routing of `NOTES.md` §3.4), and `check_theorem_1_of_inputs_of_fixed`, the same
  through the *verbatim* wiring `Work.SolutionDelivery.check_theorem_1_of_inputs` of
  `Work.StabilityFar.theorem_1_of_inputs`;
* `theorem1_of_model_data` — the same at the *model* data, from the two named analytic inputs of
  `Defs.lean` (`BiotSavartSpacetimeC1` for R3, `BiotSavartSpaceTime α` for R2) and the
  admissibility bundles of the explicit field, together with R1 and R4;
* the consistency certificates for the model data: **R4 is proved** (`timeHolderDeriv_model`),
  the far-field half of R3's input is proved (`BiotSavart.biotSavart_contDiffOn_far`), and the
  **rate rigidity** of the profile `F_*` (`Model.fstar_rate_rigid`) records the obstruction to R1
  at the delivered inhabitant (`model_rate_ne_reference`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Reductions
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_far
import Submission.Work.CoreResiduals.solVort_BSAdmissibleOnWindow
import Submission.Work.CoreResiduals.solVort_BSAdmissibleStrip
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds
import Submission.Work.SolutionDelivery.Check

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-! ## The wiring -/

/-- **The minimal residual interface produces the repaired input package.** -/
def constructedSolutionFixed_of_residuals {α : NNReal}
    {P : Work.ConstructionInstance.ProfileData α}
    (T : Work.ConstructionInstance.CoreResiduals α P) :
    Work.ConstructionInstance.ConstructedSolutionFixed α :=
  Work.ConstructionInstance.constructedSolutionFixed_of_coreResiduals T

/-- **The patched consumer** (the interface patch of `NOTES.md` §5 item 1): the delivered
`Work.SolutionDelivery.theorem_1_of_constructed` with `ConstructedSolution` replaced by the
repaired `ConstructedSolutionFixed`.  It is a *hypothesis* of the end-to-end checks below so that
this module compiles before the lead applies the patch; afterwards it is instantiated by the
patched theorem itself and the checks become literal calls. -/
def PatchedConsumer : Prop :=
  ∀ {α : NNReal}, Work.ConstructionInstance.ConstructedSolutionFixed α →
    Work.SolutionDelivery.Theorem1Statement

/-- **THE END-TO-END CHECK.**  From the minimal residual interface `CoreResiduals α P`, the range
`0 < α ≤ 1`, and the patched consumer, the challenge statement `∃ α > 0, ∃ u₀, …` of
`theorem_1` follows. -/
theorem theorem1_of_residuals (consumer : PatchedConsumer) {α : NNReal}
    {P : Work.ConstructionInstance.ProfileData α}
    (T : Work.ConstructionInstance.CoreResiduals α P) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.SolutionDelivery.Theorem1Statement :=
  consumer (constructedSolutionFixed_of_residuals T)

/-- **The four residuals, separately.**  The LWP inputs and the four named statements — the `ℝ³`
vorticity equation (R1), the spacetime Lichtenstein–Gunther class (R2), `C¹` of the ansatz on the
two-sided window (R3), and the time-Hölder regularity of `∂ₜω` on the strips (R4) — yield the
challenge statement (through the patched consumer). -/
theorem theorem1_of_four (consumer : PatchedConsumer) {α : NNReal}
    {P : Work.ConstructionInstance.ProfileData α}
    (hlwp : Work.LWP.LWPInputs α) (hv : VortEq α P) (hG : LGClass α P) (hsm : VortSmooth P)
    (hth : TimeHolderDeriv P) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1) :
    Work.SolutionDelivery.Theorem1Statement :=
  theorem1_of_residuals consumer
    { lwp := hlwp, vortEq := hv, lgClass := hG, smooth := hsm, timeHolderDeriv := hth } hα hα1

/-- **The end-to-end check through the *verbatim* wiring of `Work.StabilityFar.theorem_1_of_inputs`.**
Here `assemble` is the patched `Work.SolutionDelivery.assemblyInputs_of_constructed`
(`ConstructedSolutionFixed → AssemblyInputs`), so that
`Work.SolutionDelivery.check_theorem_1_of_inputs` — the literal elaboration of
`Work.StabilityFar.theorem_1_of_inputs` at an `AssemblyInputsα` and the scaling input — fires on
the residual data. -/
theorem check_theorem_1_of_inputs_of_fixed
    (assemble : ∀ {α : NNReal}, Work.ConstructionInstance.ConstructedSolutionFixed α →
      Work.StabilityFar.AssemblyInputs α)
    {α : NNReal} {P : Work.ConstructionInstance.ProfileData α}
    (T : Work.ConstructionInstance.CoreResiduals α P) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (hscl : Work.StabilityFar.EulerScalingToUnit) :
    Work.SolutionDelivery.Theorem1Statement :=
  Work.SolutionDelivery.check_theorem_1_of_inputs hα hα1
    (assemble (constructedSolutionFixed_of_residuals T)) hscl

/-- **The sharpest closure: only residual R1 remains.**  At the model data the challenge statement
follows from the LWP inputs and **R1 alone**: R2, R3 and R4 are theorems of this area —

* R2 is `lgClass_of_spaceTime` at the *proved* space-time Schauder input
  (`BiotSavart.biotSavartSpaceTime_holds`) and the proved strip bundle
  (`solVort_BSAdmissibleStripFull`);
* R3 is `vortSmooth_of_spacetimeC1` at the proved space-time `C¹` input
  (`BiotSavart.biotSavartSpacetimeC1_holds`), the proved half-window bundle
  (`solVort_BSAdmissibleOnWindow`) and the proved second-order time condition
  (`timeDerivLocallyLipschitz_of_inhabitant`);
* R4 is `timeHolderDeriv_of_inhabitant`.

`hR1` is the only remaining hypothesis — and as delivered it is *false* at the model data
(`Model.fstar_rate_rigid`, `Model.model_rate_ne_reference`, `ProfileData_T_eq_two`, and the cut-off
deficit): see `NOTES.md` §4 for the obstruction and §5 for the two shapes in which R1 can be
honestly stated (`VortEqWithDeficit`, or `vortEq_iff_scalar_of_decomposition`). -/
theorem theorem1_of_model_data (consumer : PatchedConsumer) {α : NNReal}
    (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3)
    (I : Inhabitant α) (hlwp : Work.LWP.LWPInputs α) (hR1 : VortEq α I.P) :
    Work.SolutionDelivery.Theorem1Statement :=
  theorem1_of_four consumer hlwp hR1
    (lgClass_of_spaceTime I.P
      (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds hα (by linarith))
      (fun S hS hST =>
        solVort_BSAdmissibleStripFull I.P (timeDerivLocallyLipschitz_of_inhabitant I) hS hST))
    (vortSmooth_of_spacetimeC1 I.P Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
      (solVort_BSAdmissibleOnWindow I.P) (timeDerivLocallyLipschitz_of_inhabitant I))
    (timeHolderDeriv_of_inhabitant I) hα (by linarith)

/-- **R2 at the model data, PROVED** — like `vortSmooth_model` for R3. -/
theorem lgClass_model {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    LGClassModel α := by
  obtain ⟨I⟩ := inhabitant_exists hα hα13
  exact ⟨I.P, inhabitant_isModelData I,
    lgClass_of_spaceTime I.P
      (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds hα (by linarith))
      (fun S hS hST =>
        solVort_BSAdmissibleStripFull I.P (timeDerivLocallyLipschitz_of_inhabitant I) hS hST)⟩

/-! ## R3 at the model data, PROVED (no residual input)

The space-time `C¹` input of R3 is *proved* (`BiotSavart.biotSavartSpacetimeC1_holds`), and so are
the two model-side conditions it consumes (the half-window admissibility bundle and the
second-order time condition).  Hence R3 holds at the model data with no residual input at all. -/

/-- **R3 at the model data, PROVED.**  `VortSmoothModel α` for `0 < α ≤ 1/3`, with every ingredient
a theorem of this area (`BiotSavart.biotSavartSpacetimeC1_holds`,
`solVort_BSAdmissibleOnWindow`, `timeDerivLocallyLipschitz_of_inhabitant`). -/
theorem vortSmooth_model {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    VortSmoothModel α := by
  obtain ⟨I⟩ := inhabitant_exists hα hα13
  exact ⟨I.P, inhabitant_isModelData I,
    vortSmooth_of_spacetimeC1 I.P
      Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds
      (solVort_BSAdmissibleOnWindow I.P) (timeDerivLocallyLipschitz_of_inhabitant I)⟩

/-! ## Certificates for the model data -/

/-- **Certificate R4 — residual R4 is a theorem at the model data.** -/
example {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    TimeHolderDerivModel α :=
  timeHolderDeriv_model hα hα13

/-- **Certificate R3-far — the far-field half of R3's input is a theorem**: outside `B(0,2R)` the
Biot–Savart field of a bounded, supported, measurable vorticity is `C¹`
(`BiotSavart.biotSavart_contDiffOn_far`). -/
theorem far_field_certificate {ω : R3 → R3} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) :
    ContDiffOn ℝ 1 (Work.LWP.biotSavart ω) {x : R3 | 2 * R < ‖x‖} :=
  Work.CoreResiduals.BiotSavart.biotSavart_contDiffOn_far hR hM hbdd hs hm

/-- **Certificate — every model-side hypothesis of the sharpest closure is a proved statement.**
For any inhabitant, the three admissibility/second-order conditions that `theorem1_of_model_data`
asks about the explicit field are theorems of this area: the half-window bundle, the second-order
time condition, and the strip bundle. -/
example {α : NNReal} (I : Inhabitant α) :
    BSAdmissibleOnWindow (solVort I.P) I.P.R I.P.T ∧
      TimeDerivLocallyLipschitz (solVort I.P) I.P.T ∧
        (∀ S : ℝ, 0 < S → S < I.P.T → BSAdmissibleStrip α (solVort I.P) I.P.R S) :=
  ⟨solVort_BSAdmissibleOnWindow I.P, timeDerivLocallyLipschitz_of_inhabitant I,
    fun S hS hST => solVort_BSAdmissibleStrip I.P hS hST⟩

/-- **Certificate — the *full* R2 bundle for the model data**: the strip admissibility, the
time-regularity of `∂ₜω` and the second-order time-regularity of `∂ₜω` on every strip
`0 < S < T`, i.e. exactly the hypothesis of `BiotSavartSpaceTime α`. -/
example {α : NNReal} (I : Inhabitant α) :
    ∀ S : ℝ, 0 < S → S < I.P.T → BSAdmissibleStripFull α (solVort I.P) I.P.R S :=
  fun S hS hST =>
    solVort_BSAdmissibleStripFull I.P (timeDerivLocallyLipschitz_of_inhabitant I) hS hST

/-- **Certificate R1-obstruction — the rate of the model data is not the reference rate.**  The
model modulation `λ̄(t) = 1-t/2` has rate `κ = -λ̄' = 1/2`, while the profile `F_*` is stationary at
the reference rates `(κ*,b*) = (1,1)`; `Model.fstar_rate_rigid` shows that both cannot hold with the
same stream function. -/
example {α : NNReal} (I : Inhabitant α) :
    -(deriv I.P.lam 1) ≠ Work.Stability.kappaStar 0 :=
  model_rate_ne_reference I

end Work.CoreResiduals
