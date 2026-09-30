import ChallengeDeps
import Submission.Helpers
import Submission.Work.Final.All
import Submission.Work.BridgeSquare.Final

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.Topology
open CategoryTheory AlgebraicTopology
open Metric (sphere)

namespace Submission

/-- **The challenge theorem, from a `Work.Final.FinalInputs` instance.**  Kept for callers that
have their own instance; the unconditional theorem below no longer needs one. -/
theorem aspherical_integer_homology_four_sphere_of_inputs [D : Work.Final.FinalInputs] :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere (D := D)

/-- **The challenge theorem, unconditional.**

The assembled Ratcliffe–Tschantz space `M̂` (`Work.Space.RTData`, delivered) is aspherical and an
integer homology 4-sphere.  Everything is discharged:

* the Mayer–Vietoris long exact sequence `L = Work.HomologyIso.mhatLES`, its `X`-slot `hX` and the
  two `Nonempty` identifications of its first two slots (`Work.Final.FinalInputsP`), with the two
  properties `hsurj`/`hker` of the Mayer–Vietoris map computed from
  `Work.BridgeSquare.cuspMap_surjective` and the null-homology of the cusp subtori
  (`Work.BridgeSquare.subtorusNull`), which is in turn proved from the three chain-level fibre
  identities `fibreLoopIdentA`, `fibreLoopIdentB`, `planeIdentT` (see
  `Submission/Work/BridgeSquare/Final.lean` and its `NOTES_SESSION4.md`);
* the smoothness of the Levi-Civita connection and the parametric curvature bound (delivered).

The originally requested interface — the bridge square `Work.FinalWire.SquareOf` — is *not*
provable for the delivered opaque identifications (`Submission/Work/BridgeSquare/NOTES.md` §2); the
`Work.Final.FinalInputsP` route used here does not need it and is strictly stronger. -/
theorem aspherical_integer_homology_four_sphere :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.BridgeSquare.aspherical_integer_homology_four_sphere

end Submission
