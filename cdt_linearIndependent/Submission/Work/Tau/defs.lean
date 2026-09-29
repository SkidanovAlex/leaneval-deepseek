import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.FineHolonomy

/-!
# Area Tau: shared imports

Bridge module for the `Work.Tau` area: imports the blueprint contracts
(`Submission.CDTPlan.Interfaces`, which defines `tauFlat`, `tauSharpAt`, `bC`, `eC`, `bA`, `eA`
and the target `TauValues`) and the already-proved development module
`Submission.CDT.FineHolonomy` / `Submission.CDT.IntegratedLcm` defining and evaluating the
paper's `integrated lcm` `I_u^v(w)` (its `harmonicFun` and `correctionFun` halves).

The two copies of `integrated lcm` (the contract's `Submission.CDTPlan.integratedLcm` and the
development's `Submission.CDT.IntegratedLcm.integratedLcm`) are *definitionally equal*, so the
lemmas proved about the latter are usable for the former by `rfl`; the bridges below record that.
-/

namespace Work.Tau

/-- The contract's `integratedLcm` is definitionally the development's. -/
theorem cdtPlan_integratedLcm_eq (u v w : ℝ) :
    Submission.CDTPlan.integratedLcm u v w = Submission.CDT.IntegratedLcm.integratedLcm u v w := rfl

/-- The contract's `harmonicFun` is definitionally the development's. -/
theorem cdtPlan_harmonicFun_eq :
    Submission.CDTPlan.harmonicFun = Submission.CDT.IntegratedLcm.harmonicFun := rfl

/-- The contract's `correctionFun` is definitionally the development's. -/
theorem cdtPlan_correctionFun_eq :
    Submission.CDTPlan.correctionFun = Submission.CDT.IntegratedLcm.correctionFun := rfl

end Work.Tau
