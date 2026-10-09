import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFT.Inclusion.hilbert90_cocycle
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.HassePrinciple.CyclicBase
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.HBNUnits_from_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Dependency cone for the `C₂`-Hasse bricks

A single module collecting the imports a prover of `ExtChain.c2_hasse_brick` and
`ExtChain.c2_h90_brick` is expected to need: the idèle/class-group vocabulary of the class
formation, the cyclic Hasse norm result, the idèle-level Hilbert 90 and the fixed-field
machinery of `Mathlib` (via `Mathlib` itself).
-/

set_option autoImplicit false
