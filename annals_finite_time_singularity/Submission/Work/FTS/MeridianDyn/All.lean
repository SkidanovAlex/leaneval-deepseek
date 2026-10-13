/-
# `Work.FTS.MeridianDyn.All` — umbrella import of the dynamic meridian bridge

Import this module to get the whole area:

* the vocabulary (`Defs`): `dynVort`, `dynPsi`, `DynEqF`, `dynEqLHS`, `MeridianEqOn`,
  `merPsi`, `merProfileDyn`, `ProfDerivData`, `VorticityEquationAt`/`On`;
* the five chain rules (`Chain/`), the algebraic core (`Algebra/`), the parity lemmas (`Odd/`);
* the static `g`-equation bridge (`Bridge/`), the clock and regularity extraction
  (`Clock/`, `Smooth/`);
* the meridian residual of the dynamical ansatz (`ResidDyn`);
* the dynamic profile equation `(E)` and its derivation from the fake-time equation (`DynEqF`);
* the constant-rate sanity check (`Const`) and the transport back to `ℝ³` (`Vort`);
* **the main theorem `meridianEq_of_dynEq`** (`Main`).

See `NOTES.md` for the interface, the conventions, and the one substantive caveat
(the `L₁₂`-zero-mode hypothesis `hL12`, and the correction constant `muDynStar`).
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.Algebra.meridianResid_algebra_dyn
import Submission.Work.FTS.MeridianDyn.Chain.timeDeriv_dynVort
import Submission.Work.FTS.MeridianDyn.Chain.pdR_dynVort
import Submission.Work.FTS.MeridianDyn.Chain.pdZ_dynVort
import Submission.Work.FTS.MeridianDyn.Chain.pdR_dynPsi
import Submission.Work.FTS.MeridianDyn.Chain.pdZ_dynPsi
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd_win
import Submission.Work.FTS.MeridianDyn.Bridge.gRHS_sub_gDynRHS
import Submission.Work.FTS.MeridianDyn.Bridge.mainLHS_sub_N_eq
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.MeridianDyn.Clock.amplitude_hasDerivAt
import Submission.Work.FTS.MeridianDyn.Clock.scale_hasDerivAt
import Submission.Work.FTS.MeridianDyn.Smooth.profFamOdd_contDiffAt
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.FTS.MeridianDyn.DynEqF
import Submission.Work.FTS.MeridianDyn.Const
import Submission.Work.FTS.MeridianDyn.Vort
import Submission.Work.FTS.MeridianDyn.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
