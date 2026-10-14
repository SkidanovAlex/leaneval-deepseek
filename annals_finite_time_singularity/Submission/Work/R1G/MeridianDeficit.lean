import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.R1G.Defs
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.Support
import Submission.Work.R1G.vorticity_psiField_bslOp

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

/-- **The G-route's residual in meridian form.**  The meridian residual of the constructed (cut)
field, against its own meridian stream function `Ψ`, is the *explicit* cut-off deficit
`Defs.cutDeficit`: the local statement of the deficit cancellation. -/
def MeridianDeficitIdent (P : Work.ConstructionInstance.ProfileData α)
    (Ψ W : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ r z t : ℝ, 0 < r →
    Work.CoreResiduals.meridianResid (cutProfile P W) Ψ r z t = cutDeficit P Ψ W r z t





/-! ## The G-route's honest residual interface -/

/-- **The G-route's honest residual interface.**  The modulated data (`g ≠ 0` solving the `St2`/`St3`
`g`-equation with vanishing far-field term), the two halves of the ansatz dictionary (the velocity is
the stream-function field of `Ψ`, the vorticity is the cut meridian profile `χ(ρ/L)·W`), and the
**meridian residual** `MeridianDeficitIdent`: the constructed field's residual *is* the explicit
cut-off deficit.

Unlike `Defs.DeficitIsGResidual` (the strong field-level form used by `Check.GRouteHyp`, which forces
the deficit to be a function of the self-similar variable and is therefore *false* for a cut field),
this interface is non-vacuous and is exactly what the local computation of `Work.R1G.CutDeficit`
supports (`ModulatedData.meridianDeficitIdent_of_far_zero` proves its self-similar instance).  The
deficit it produces is **nonzero on the annulus** `L ≤ ρ ≤ 2L` (`Work.R1G.Support`), i.e. the
interface explains *why* the zero-deficit residual R1 fails at a cut field — and R1 *closes*
precisely when the modulation also cancels the annulus contribution. -/
structure GRouteResidual (α : NNReal) where
  /-- the modulated profile data (`g ≠ 0` solving the `g`-equation) -/
  D : ModulatedData α
  /-- the `g`-equation's far-field term vanishes (the modulation cancels the profile residual) -/
  hFar : ∀ z θ : ℝ, D.Far z θ = 0
  /-- the meridian stream function of the constructed velocity -/
  Ψ : ℝ → ℝ → ℝ → ℝ
  /-- the meridian profile of the *uncut* constructed vorticity -/
  W : ℝ → ℝ → ℝ → ℝ
  /-- the ansatz half of the dictionary: the velocity is the stream-function field of `Ψ` -/
  hv : ∀ x t, Work.ConstructionInstance.ansatzV D.P x t = Work.Cyl.cylField
    (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
    (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x
  /-- the ansatz half of the dictionary: the vorticity is the cut meridian profile -/
  hω : ∀ x t, Work.ConstructionInstance.solVort D.P x t
    = cutProfile D.P W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x
  /-- the stream function is `C²` in the meridian variables -/
  hΨ : ∀ t r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2 t) (r, z)
  /-- the meridian profile is differentiable in the meridian variables -/
  hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => cutProfile D.P W r z t) r z
  /-- **the honest residual**: the meridian residual is the explicit cut-off deficit -/
  hMer : MeridianDeficitIdent D.P Ψ W




/-! ## The deficit cancellation at the profile level -/


end Work.R1G
