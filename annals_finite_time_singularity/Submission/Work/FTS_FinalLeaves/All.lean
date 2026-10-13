/-
# `Submission.Work.FTS_FinalLeaves.All` — the whole `FTS_FinalLeaves` chapter in one import

Subproject **FTS_FinalLeaves** (curric-46 lead brief): the research-free *final leaves* of the
`FinalV2` integration layer.  For each of the seven producer statements of the frozen
`Submission/Work/FTS/FinalV2/Producers.lean` (which must not be edited) this chapter contains a
theorem `<name>_proved` with the **identical elaborated type**, proved `sorry`-free and
axiom-clean (`#print axioms = [propext, Classical.choice, Quot.sound]`).

| frozen producer (`Work.FTS.FinalV2.*`) | proved here (`Work.FTS_FinalLeaves.*`) | file | conjunct |
|---|---|---|---|
| `kernel_exists` | `kernel_exists_proved` | `kernel_exists_proved.lean` | (0) |
| `classC_sup_le` (feed of (5′)) | `classC_sup_le_proved` | `classC_sup_le_proved.lean` | (5′) feed |
| `sup5'` | `sup5'_proved` | `Sup5.lean` | (5′) |
| `mu6'` | `mu6_proved` | `mu6_proved.lean` | (6′) |
| `psiCan_C3` | `psiCan_C3_proved` | `psiCan_C3_proved.lean` | (13′) |
| `merPsi_C3` | `merPsi_C3_proved` | `merPsi_C3_proved.lean` | (10′) |
| `sol_fire` | `sol_fire_proved` | `sol_fire_proved.lean` | (8′) feed |
| `profDerivData_min` | `profDerivData_min_proved` | `profDerivData_min_proved.lean` | (8′) feed |

(The bare `_(name)_proved` above is short for `Work.FTS_FinalLeaves.<name>_proved`.)

## How to consume

Replace each `Work.FTS.FinalV2.<name>` occurrence on the `WireSkeleton`/`Mer8` path by
`Work.FTS_FinalLeaves.<name>_proved`; the statements have been checked to be *the same type*
(`_scr/typecheck.lean` re-derives each producer statement verbatim from the `_proved` theorem).
`Work.FTS.FinalV2.classC_sup_le` is not itself reached by the wire (as recorded in
`fts_v2_install.md` §5); it is proved here so that `sup5'_proved` can consume it.

## Verification records

* `_scr/typecheck.lean` — each producer statement copied verbatim from
  `FinalV2/Producers.lean` (same `open`s and variable context), proved by the `_proved` theorem.
  Elaborates with `rc = 0`.
* `_scr/axcheck.lean` — `#print axioms` of all eight declarations; every one reports
  `[propext, Classical.choice, Quot.sound]`.
* `_scr/` additionally holds throwaway reconnaissance probes (some retired to comments); it is
  not part of the deliverable.

See `NOTES.md` in this directory for the route of each leaf and for the auxiliary modules that
the leaf proofs introduced.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS_FinalLeaves.kernel_exists_proved
import Submission.Work.FTS_FinalLeaves.classC_sup_le_proved
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved
import Submission.Work.FTS_FinalLeaves.merPsi_C3_proved
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_FinalLeaves.sol_fire_proved
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_FinalLeaves.Sup5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
