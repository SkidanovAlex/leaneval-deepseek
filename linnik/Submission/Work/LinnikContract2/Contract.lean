/-
# LinnikContract2 — Contract.lean

**Single import surface for the round-2 chapter.**  Import
`Submission.Work.LinnikContract2.Contract` to get:

* the round-2 definitions of §3.0 (`Defs.lean`): `lamOf`, `zeroMult`, `IsZ`, `IsZH H`, `IsZW`,
  `IsMin1H H`, `IsMin1`, `IsMin1N`, `Lam0Bound`, `Lam2Bound`, `Lam3Bound`, `Ncount`, `lamMax`,
  `lamChar`, `wHB`, `F2`, `Hk`, `Bfun`, `InBox`, `boxSum`, `boxAbs`, `SiegelZero`;
* the areas (`Areas.lean`): `Area0 = WideMinExists` (**proved**, `Numbering.lean`), `Area1` …
  `Area7`, and the certificates
  `ZeroFreeCert` (with the clauses `Z1`–`Z5`), `DensityCert` (with `D1`, `D2`), `PerCharCert`,
  `SiegelCase`, `Assembly`, together with the tables `rows15`, `rows14`, `table13`;
* the round-2 interface (`API.lean`) — projections of `IsMin1`, monotonicity of the height family,
  and the `(D2)`-hypothesis interface `d2_hyp_of_isMin1`/`d2_hyp_of_isMin1H`;
* the HB §6 formalisation (`HB6.lean`): `IsZRect`, `IsMin1Rect`, `wide_min_of_rect`,
  `isMin1_of_isMin1Rect_of_isZ`;
* the §6 numbering (`Numbering.lean`): `area0 : Area0` — the wide minimiser exists, a theorem, so
  the contract carries no numbering input;
* the composition (`Compose.lean`), **proved**:
  `linnik_of_areas (h1 : Area1) … (h7 : Area7) : ∃ c, ∀ a d, 0 < a → a < d →
  a.Coprime d → p a d ≤ c * d^(5.5)` — seven hypotheses, no more (`Area0` is a theorem and the
  §14/§15 setting clause `NumZeroNarrow` has been deleted);
* the **window** (`A7/`): `window_step` (the §15 step at the narrow minimiser, the honest zero
  count), `WindowAPI` (the transfer lemmas `lam2Bound_narrow_of_wide`, `lam3Bound_narrow_of_wide`,
  `lamOf_narrow_ge`, `Ncount_le_table_w`), `WindowCert` (the five numerical certificates
  `win_g1`–`win_g5`) and `WindowAssembly` (`area7_window`, the unconditional assembly);
* `Area7`, **re-proved** against the round-2 contract (`A7/Area7Final.lean`:
  `area7 := A7.area7_window`);
* `Area5`, transported from the round-1 proof (`CarryOver.lean`);
* the transports of the round-1 development (`Bridge.lean`) and of the round-1 proved results
  (`CarryOver.lean`), the non-vacuity statements (`Satisfiability.lean`) and the frozen
  specification (`Spec.lean`).
-/
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.HB6
import Submission.Work.LinnikContract2.Numbering
import Submission.Work.LinnikContract2.Spec
import Submission.Work.LinnikContract2.Compose
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikContract2.CarryOver
import Submission.Work.LinnikContract2.Satisfiability
import Submission.Work.LinnikContract2.A7.Area7
import Submission.Work.LinnikContract2.A7.table13_col_le
import Submission.Work.LinnikContract2.A7.sec15_caseB_large
import Submission.Work.LinnikContract2.A7.area7_of_isZ_or_large
import Submission.Work.LinnikContract2.A7.sec15_caseB
import Submission.Work.LinnikContract2.A7.area7_of_isZ_or_largeLam1
import Submission.Work.LinnikContract2.A7.area7_of_narrowOrSmall
import Submission.Work.LinnikContract2.A7.window_step
import Submission.Work.LinnikContract2.A7.WindowCert
import Submission.Work.LinnikContract2.A7.WindowAssembly
import Submission.Work.LinnikContract2.A7.Area7Final

open Work.LinnikContract2

-- `linnik_of_areas` uses only the three permitted axioms (`config.json`).
#print axioms linnik_of_areas
-- the §15 step at the narrow pivot (the window's core)
#print axioms Work.LinnikContract2.A7.window_step
-- the five window certificates
#print axioms Work.LinnikContract2.A7.win_g1
#print axioms Work.LinnikContract2.A7.win_g4
-- the unconditional assembly (the window closed)
#print axioms Work.LinnikContract2.A7.area7_window
-- the proved §6 numbering
#print axioms area0
-- the assembly (Case A: the numbered zero lies in the working region)
#print axioms area7_of_isZ
-- the assembly in Case A or with a large wide minimum (lambda_1 >= 43/40)
#print axioms Work.LinnikContract2.A7.area7_of_isZ_or_large
-- the assembly in Case A or with lambda_1 >= 29/50 (the best frozen-input window)
#print axioms Work.LinnikContract2.A7.area7_of_isZ_or_largeLam1
-- the assembly under HB's own 14/15 setting assumption (lambda_1 < 0.348 or the numbered zero is narrow)
#print axioms Work.LinnikContract2.A7.area7_of_narrowOrSmall
-- AREA 7, re-proved (the contract's Area 7 now contains HB's 14/15 setting clause NumZeroNarrow)
#print axioms Work.LinnikContract2.area7
-- the Case-B ingredients (crude branch; narrow pivot with the transferred clauses)
#print axioms Work.LinnikContract2.A7.sec15_caseB_large
#print axioms Work.LinnikContract2.A7.sec15_caseB
#print axioms Work.LinnikContract2.A7.table13_col_le
-- the transported per-character certificate
#print axioms area5
-- the HB §6 ⟹ §12 bridge (the mathematical content of the round-2 fix)
#print axioms wide_min_of_rect
