/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak.aeEnergyWAux` — thin re-export

This module is *identical* in content to
`Submission/Work/FTS/EllipticEst/Honest/Step1G/AeClear/AeEnergyWAux.lean` (the two were
byte-identical copies, both in the namespace `Work.FTS.EllipticEst.AngAWeak`).  Two modules
declaring the same global names cannot coexist in one environment, and several modules import
both, so the body has been moved to the `AeClear` copy and this module is kept as a re-export
for the many existing consumers.

The original body is preserved (as data, not as a module) in
`AngAWeak/aeEnergyWAux.lean.bak.txt`.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
