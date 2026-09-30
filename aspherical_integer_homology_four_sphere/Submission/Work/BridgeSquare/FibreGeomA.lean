/-
# `BridgeSquare/FibreGeomA.lean` — vocabulary of the `κ_{v,2}` fibre identity (`A`-case)

This module only re-exports `Submission.Work.BridgeSquare.FibreGeomDataA`, which holds the actual
definitions (`axVec`, `cuspCorner`, `cuspCorner1`, `cuspMid`, `lam2V`, `edgeBit`, `cubeCornerPt`,
`cubeCornerPt1`) together with the numeric facts proved about them on the generated tables.

It is kept as a separate module because the downstream modules (`singA_eq_cChain.lean`) were
written against this path; the definitions all live in `FibreGeomDataA`.
-/
import Submission.Work.BridgeSquare.FibreGeomDataA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

