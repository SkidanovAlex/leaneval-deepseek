import Submission.Work.Homology.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.Point
import Submission.Work.Homology.RelChainMap
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.SingHomologyHomeomorph
import Submission.Work.Homology.SingHomologyCoproduct
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Homology.ContractibleHomology
import Submission.Work.Homology.BallHomology
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.Homology.HomotopyEquivHomology
import Submission.Work.Homology.DeformationRetractHomology
import Submission.Work.Homology.AffineSimplexMap
import Submission.Work.Homology.SimplexShim
import Submission.Work.Homology.Bridge
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.MayerVietoris

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Singular homology toolkit: aggregate import

Import this module to get the whole `Work.Homology` chapter.

## Main entry points

* `Work.Homology.intHomology_eq` — the bridge
  `LeanEval.Topology.intHomology k X = singHomology ZMod k X`.
* `Work.Homology.relChain`, `Work.Homology.relHomology` — relative chains and homology.
* `Work.Homology.pairSeq_shortExact`, `Work.Homology.pairHomHX_exact`,
  `Work.Homology.pairHomRel_exact`, `Work.Homology.pairHomA_exact` — the long exact sequence of a
  pair, and `Work.Homology.pairSeqMap`, `Work.Homology.pairδ_naturality`,
  `Work.Homology.relProjHom_naturality` for its naturality in maps of pairs.
* `Work.Homology.MayerVietoris.mv_exact_HX`, `Work.Homology.mv_exact_Hrel`,
  `Work.Homology.mvShort_shortExact` — Mayer–Vietoris.
* `Work.Homology.singHomologyZeroIsoOfPathConnected`, `Work.Homology.singHomologyPoint`,
  `Work.Homology.SingHomologyCoproduct`, `Work.Homology.SingHomologyClopen` — additivity and
  degree zero.
* `Work.Homology.SingHomologyHomeomorph`, `Work.Homology.HomotopyEquivHomology`,
  `Work.Homology.DeformationRetractHomology`, and their `intHomology` wrappers
  `Work.Homology.intHomology_iso_of_homeomorph`, `Work.Homology.intHomology_iso_of_homotopyEquiv`,
  `Work.Homology.intHomology_iso_of_deformationRetract` — invariance.
* `Work.Homology.singHomology_sphere`, `Work.Homology.intHomology_sphere_four`,
  `Work.Homology.relHomology_disc_sphere`, `Work.Homology.relHomology_excision` — spheres,
  disc pairs and excision.
* `Work.Homology.singChain_eq`, `Work.Homology.relChain_eq` — the `rfl` bridges to the ported
  `Work.Cohomology` subdivision/excision chapter.
-/

namespace Work.Homology

end Work.Homology
