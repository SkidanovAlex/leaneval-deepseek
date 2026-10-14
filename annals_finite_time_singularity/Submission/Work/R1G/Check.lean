import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.Check
import Submission.Work.R1G.Defs
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.MeridianDeficit

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





/-! ## At the delivered inhabitant: the mechanical rewrite -/



/-! ## At the modulated data: R1 by the G-route, R2/R3 as theorems

The honest (modulated) data is a *different* `ProfileData` from the delivered inhabitant (`g ≠ 0`
versus `g = 0`), so R2/R3/R4 must be read at *its* field `solVort G.D.P`.  The two analytic inputs
of `Work.CoreResiduals` (`biotSavartSpaceTime_holds`, `biotSavartSpacetimeC1_holds`) and the two
bundles are proved for the *general* `ProfileData` (`solVort_BSAdmissibleStripFull`,
`solVort_BSAdmissibleOnWindow`), so **R2 and R3 are theorems at the modulated data as well**, the
only extra input being the second-order joint-`C¹` condition
`TimeDerivLocallyLipschitz (solVort G.D.P) G.D.P.T`; R4 (finding H) remains the caller's.  This is
the honest form of `Work.CoreResiduals.theorem1_of_model_data` with `hR1` closed by the G-route. -/

end Work.R1G
