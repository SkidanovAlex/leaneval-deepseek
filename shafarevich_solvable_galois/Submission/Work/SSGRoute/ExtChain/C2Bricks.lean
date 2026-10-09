import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtChain.c2_h90_brick
import Submission.Work.SSGRoute.ExtChain.c2_hasse_brick
import Submission.Work.SSGRoute.ExtChain.c2_adapted_basis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

/-!
# The arithmetic and lattice inputs of the degree-one Hasse principle at `C₂`

Three inputs used by `ExtChain.c2_lattice_lift`:

* `c2_adapted_basis` — the `ℤ`-lattice structure theory (a basis adapted to an involution);
* `c2_hasse_brick` — Hasse's norm principle at an involution of a finite Galois extension;
* `c2_h90_brick` — Hilbert 90 at an involution (norm-`1` units are coboundaries).

Each is proved in a sibling module of the same name; this module collects them for
`ExtChain.c2_lattice_lift`.
-/
