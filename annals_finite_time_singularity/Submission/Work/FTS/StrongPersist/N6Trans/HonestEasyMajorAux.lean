/-
Auxiliary module for `HonestEasyMajorLem` (`Submission/Work/FTS/StrongPersist/N6Trans/`).

It contains `honest` (open-quadrant) copies of the `2`-dimensional `T1Easy`-assembly of
`Submission/Work/H2/T1Q/`:

* `AssemblyQ_o`, `xD_summand_bound_q_o`, `yM_summand_bound_q_o` and the public helpers
  `slotIntBoundQ_o`, `ae_pm_z_pos_o`, `xD_aesm_q_o`, `yM_aesm_q_o`, `xD_Kf_int_q_o`,
  `xD_Kg_int_q_o`, `yM_Kf_int_q_o`, `yM_Kg_int_q_o` : source
  `Submission/Work/H2/T1Q/AssemblyQ.lean`;
* the two continuity twins `continuousOn_dzIter_qd_open`, `continuousOn_mixed_qd_open`.

Three changes are made to the source (see the generated files for the block boundaries):

1. the unused hypothesis `Work.Spaces.DecayAll 4 f` is deleted from the three statements
   `xD_summand_bound_q`, `yM_summand_bound_q`, `AssemblyQ` (it never occurs in any proof body);
2. the class hypothesis `Work.FTS.LocData.SmoothQuad` (`C^∞` on `z > -1`) is replaced by
   `Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on `z > 0`), which is what the honest level-six
   chapter supplies.  The only places where this needs more than a textual change are the two
   continuity lemmas `continuousOn_dzIter_qd`, `continuousOn_mixed_qd`, quoted above in their
   open-class form (for `SmoothOpen` the uncurried slot is continuous on `quadQ` directly);
3. the exceptional summand is bounded by `ExcBoundOpen`
   (`Submission/Work/FTS/StrongPersist/N6Trans/OpenTwins/ExcBoundOpen.lean`) instead of
   `Work.H2.T1Q.ExcBoundQ`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmB
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
