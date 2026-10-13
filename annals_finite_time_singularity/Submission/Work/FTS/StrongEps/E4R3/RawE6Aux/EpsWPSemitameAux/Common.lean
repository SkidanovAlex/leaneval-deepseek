/-
Copyright: work module for the Elgindi finite-time singularity project.

# `RawE6Aux/EpsWPSemitameAux/Common.lean` — shared imports of the semi-tame estimate

The target `Work.FTS.StrongEps.E4R3.RawE6Aux.epsWP_semitame_aux` (leaf S2 of the `Apriori4`
chapter) is proved by assembling the five `BData` producers of the blocks of `epsWBlk`.  This
module collects the imports shared by the pieces:

* `Apriori4Proofs.Defs` — `epsWBlk`, the five blocks, `BData`, `sum5`, `epsWP_eq_epsWBlk`;
* `Apriori4Proofs.L6Ctx_JfamP_proof` — `Pz_Jeps_eq_zero_of_not_mem_quadrant`;
* `StrongPersist.H6Aux.Facts` — the level shifts `HkSq_Dth_le_succ'`, `HkSq_Dz_le_succ'`;
* `StrongPersist.H6Rows.AK6Row`, `StrongPersist.L3Aux.Transport_L12_zero_le`,
  `StrongEps.HkSq_const_mul`, `GalFields.RHS.HkSum`, `OpenPkg.Basic` — the analytic inputs.

See `RawE6Aux/NOTES_bdata_blocks.md` for the routes.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
