import Mathlib
import Submission.StripCrosscut
import Submission.TrisecantStructure
import Submission.TrisecantTransverse
import Submission.Work.Drive.isPathConnected_component_liftedTrisecant
import Submission.Work.Drive.no_translate_path_in_lifted_trisecant
import Submission.Commons.Topology.Strip.strip_crosscut_bounded_away
import Submission.Commons.Topology.Strip.strip_crosscut_of_closure_components_bdd

/-!
# API module for the no-inflection brick (d)

Re-exports the definitions and theorems of the (fixed) `Submission` modules, and the proved
`Work.Drive` / `Commons` lemmas, that the lemmas
`Work.Drive.shortSecantsFree_of_noInflection` and
`Work.Drive.stripCrosscutAvoidingO_of_generic_noInflection` are stated in terms of, so that those
statements need no cross-directory `depends_on` entries.  Nothing new is proved here.

Available to the prover of those two statements:

* `LeanEval.KnotTheory.Quadrisecant.liftedTrisecant r` — the preimage in the strip
  `ℝ × (0, period)` of Kuperberg's trisecant locus `O = trisecantSet r` under the covering
  `stripSecantClass`.
* `LeanEval.KnotTheory.Quadrisecant.StripCrosscutAvoidingO r` — the residual two-dimensional
  statement (a bottom-to-top crosscut of the strip with interior avoiding `liftedTrisecant r`).
* `Submission.Work.Drive.isPathConnected_component_liftedTrisecant` — every connected component of
  `liftedTrisecant r` is path connected (under `IsSmoothKnot`, `QuadrisecantFree`,
  `TorusGeneralPositionTransverse`).
* `Submission.Work.Drive.no_translate_path_in_liftedTrisecant` — no point of `liftedTrisecant r` is
  joined inside it to its own translate `(z.1 + period, z.2)` (same hypotheses).
-/

open LeanEval.KnotTheory.Quadrisecant
