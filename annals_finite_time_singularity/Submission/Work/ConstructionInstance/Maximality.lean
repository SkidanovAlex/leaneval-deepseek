/-
# `Work.ConstructionInstance.Maximality` — the maximality residual, discharged

`Tie.lean` decomposed `tie` into four analytic inputs plus the maximality of `T`
(`SelfSimMaximal`).  This module proves that the fourth input is **not needed**: it is a *theorem*
given the first three.

The mathematical content is that the spacetime Lichtenstein–Gunther class of a solution bounds its
derivative *quantitatively* (`IsContDiffHolderOn` carries `IsBoundedFunOn (fderivWithin …)`), so no
solution of the cut-off datum can live past `P.T`:

* if an `LGClass`-solution `u'` of the datum existed on `[0,T')` with `P.T < T'`, then
  `LWPInputs.uniqueness` (both are LG-class solutions with datum `BS ω₀`) would force
  `u' = ansatzV P` on `[0,P.T)` — this is where residual 3 (`SelfSimVortSmooth`) and the
  pressure reconstruction (`LWPInputs.pressure`, fed by residuals 1 and 2) enter;
* the strip `[0,P.T]` is *contained* in `[0,T')`, so the LG class of `u'` bounds its derivative —
  hence its vorticity (`norm_vorticity_le`) — on that strip by a constant `3C`;
* but on `[0,P.T)` the vorticity of `u'` is `solVort P` (the Biot–Savart law), whose sup-norm
  dominates `c₀α/(2(P.T-t))` by `St5` (`solVort_hansatz` + `hlam_le`) — contradiction for `t → P.T⁻`.

Hence `SelfSimNoLG P → SelfSimBlowUp P → SelfSimMaximal P`, and the residual interface of the
construction drops to `CoreResiduals`: the LWP inputs and the **four** analytic outputs
`vortEq` (Stability), `lgClass` (LWP), `smooth` (Construction), and — finding (H) —
`timeHolderDeriv` (the `St1`/`St3` second-order estimate of the modulation).
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.selfSimNoLG_of_data

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The maximality residual is a theorem -/

/-- **Maximality from the four analytic inputs** (the chain
`SelfSimNoLG → SelfSimBlowUp → SelfSimMaximal`). -/
theorem selfSimMaximal_of_data {α : NNReal} (P : ProfileData α) (hlwp : Work.LWP.LWPInputs α)
    (hv : SelfSimVorticityEquation α P) (hG : SelfSimLGClass α P) (hsm : SelfSimVortSmooth P) :
    SelfSimMaximal P :=
  selfSimMaximal_of_blowUp P hlwp hv hG hsm
    (selfSimBlowUp_of_noLG P (selfSimNoLG_of_data P hlwp hv hG hsm))

/-- **`tie` from the four analytic inputs alone** (no maximality hypothesis). -/
theorem selfSimilarEulerSolution_of_data {α : NNReal} (P : ProfileData α)
    (hlwp : Work.LWP.LWPInputs α) (hv : SelfSimVorticityEquation α P)
    (hG : SelfSimLGClass α P) (hsm : SelfSimVortSmooth P) :
    SelfSimilarEulerSolution α P.T P :=
  selfSimilarEulerSolution_of P hlwp hv hG hsm (selfSimMaximal_of_data P hlwp hv hG hsm)

/-! ## The minimal residual interface -/

/-- **The residual interface of the construction, in its minimal form.**  There is no maximality
field: it is derived (`selfSimMaximal_of_data`).  The five fields are the LWP chapter's analytic
inputs (whose own residual list is `Work.LWP.NOTES.md`) and the four analytic outputs of the sibling
chapters that this directory cannot prove:

* `vortEq` — the ℝ³ vorticity equation for `u = BS ω` (`Work.Stability`'s `St0`–`St3` bootstrap);
* `lgClass` — the spacetime Lichtenstein–Gunther class, `Work.LWP.SpaceTimeHolder` (`Work.LWP`);
* `smooth` — `C¹` of the ansatz on the two-sided window (the construction's backward extension);
* `timeHolderDeriv` — the time-Hölder regularity of `∂ₜω` on the strips, equivalently a
  strip-uniform bound on `∂ₜ²ω` (finding (H); the `St1`/`St3` second-order estimate).

Everything else is a theorem of this directory: `ProfileData` is inhabited
(`profileData_inhabited`) and every field about the vorticity — including, by this module,
maximality — is derived. -/
structure CoreResiduals (α : NNReal) (P : ProfileData α) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- **residual 1**: the ℝ³ vorticity equation (`Work.Stability`'s bootstrap) -/
  vortEq : SelfSimVorticityEquation α P
  /-- **residual 2**: the spacetime Lichtenstein–Gunther class of `BS(ω(·,t))` (`Work.LWP`) -/
  lgClass : SelfSimLGClass α P
  /-- **residual 3**: `C¹` of the ansatz velocity on the two-sided window (backward extension) -/
  smooth : SelfSimVortSmooth P
  /-- **residual 4 (finding H)**: the time-Hölder regularity of `∂ₜω` on the strips -/
  timeHolderDeriv : SelfSimTimeHolderDeriv P

/-- **`tie` from the minimal residual interface.** -/
theorem tie_of_coreResiduals {α : NNReal} {P : ProfileData α} (T : CoreResiduals α P) :
    SelfSimilarEulerSolution α P.T P :=
  selfSimilarEulerSolution_of_data P T.lwp T.vortEq T.lgClass T.smooth

/-- **The patched input package from the minimal residual interface.** -/
def constructionDataFixed_of_coreResiduals {α : NNReal} {P : ProfileData α}
    (T : CoreResiduals α P) : ConstructionDataFixed α :=
  { lwp := T.lwp
    prof := P
    tie := tie_of_coreResiduals T
    hThDt := T.timeHolderDeriv }

/-- **The constructed-solution package from the minimal residual interface.** -/
def constructedSolutionFixed_of_coreResiduals {α : NNReal} {P : ProfileData α}
    (T : CoreResiduals α P) : ConstructedSolutionFixed α :=
  constructedSolutionFixed (constructionDataFixed_of_coreResiduals T)

/-- The `maximal` field of `TieInputs` is redundant: dropping it gives `CoreResiduals`. -/
def coreResidualsOfTieInputs {α : NNReal} {P : ProfileData α} (T : TieInputs α P) :
    CoreResiduals α P :=
  { lwp := T.lwp
    vortEq := T.vortEq
    lgClass := T.lgClass
    smooth := T.smooth
    timeHolderDeriv := T.timeHolderDeriv }

/-- The same, in the paper's (blow-up) form of the fourth residual. -/
def coreResidualsOfBlowUpInputs {α : NNReal} {P : ProfileData α} (T : TieInputsBlowUp α P) :
    CoreResiduals α P :=
  { lwp := T.lwp
    vortEq := T.vortEq
    lgClass := T.lgClass
    smooth := T.smooth
    timeHolderDeriv := T.timeHolderDeriv }

/-! ## Certificates -/

/-- **Certificate I — maximality is derived, not assumed.** -/
example {α : NNReal} (P : ProfileData α) (hlwp : Work.LWP.LWPInputs α)
    (hv : SelfSimVorticityEquation α P) (hG : SelfSimLGClass α P) (hsm : SelfSimVortSmooth P) :
    SelfSimMaximal P :=
  selfSimMaximal_of_data P hlwp hv hG hsm

/-- **Certificate J — the minimal residual interface produces the whole package.** -/
example {α : NNReal} {P : ProfileData α} (T : CoreResiduals α P) : ConstructedSolutionFixed α :=
  constructedSolutionFixed_of_coreResiduals T

/-- **Certificate K — `TieInputs` (with the maximality hypothesis) is equivalent to the minimal
interface**: the hypothesis is redundant. -/
example {α : NNReal} {P : ProfileData α} (T : TieInputs α P) :
    SelfSimilarEulerSolution α P.T P :=
  tie_of_coreResiduals (coreResidualsOfTieInputs T)

end Work.ConstructionInstance
