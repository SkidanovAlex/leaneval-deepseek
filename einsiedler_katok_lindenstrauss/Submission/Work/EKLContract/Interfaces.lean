/-
# `Work.EKLContract` — the FROZEN interface for `einsiedler_katok_lindenstrauss`

Import this module to obtain the frozen component `Prop`s, the basic API for `SL₃(ℝ)`,
`aDiag`, the root groups `U_ij`, and the glue.

* `Work.EKLContract.Defs`        — the frozen definitions and the component `Prop`s `P_*`.
* `Work.EKLContract.Diag`        — the elementary API (`toMat`, `aDiag_add`, `aPlus_mul_a0`, …).
* `Work.EKLContract.Glue`        — `rigidity_of`, `posEntMeasure_of`, `lowEntropy_of`,
  `not_posEnt_Drho`, `ekl_of_components`, `ekl_challenge` (all proved).
* `Work.EKLContract.Consistency` — satisfiability / non-vacuity of the interface.
* `Work.EKLContract.Entropy`     — the entropy objects at the trivial partition.
* `Work.EKLContract.All`         — everything above plus the fleet API lemmas.
* `Work.EKLContract.Lemmas.*`    — API lemmas proved by the fleet (see `All.lean`).

Every change of a statement relative to `Submission/Work/EKLPlan/Interfaces.lean` is recorded in
`NOTES.md`, with the reason.  Referee records are in `REVIEWS.md`.
-/
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Glue
