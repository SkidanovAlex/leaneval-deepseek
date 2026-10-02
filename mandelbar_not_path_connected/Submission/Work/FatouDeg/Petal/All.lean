/-
Copyright: subproject `Submission/Work/FatouDeg/Petal/` of `mandelbar_not_path_connected`.

# `Work.FatouDeg.Petal` — the multi-petal Leau--Fatou theory at exponents `m ≥ 3`

One-stop import for the port of `Submission/Work/MultiPetal/`.  Every result here is the
`Work.MultiPetal` result with the hypothesis `4 ≤ m` weakened to `3 ≤ m`; the proofs are copies of
the originals with the numerics repaired at `m = 3`.

## The headline result

* `Work.FatouDeg.Petal.fatouCoordSec3` — the exact conclusion of
  `Work.MultiPetal.fatouCoordMultiSecAux` for `3 ≤ m`: for `N_{m,G}(z) = z - z^m + z^(m+1) G(z)`
  with `3 ≤ m` and any `δ > 0` there is an open, nonempty petal `Pa ⊆ ball 0 δ` avoiding `0`
  (inside the sector `0 < Re z`, `m|Im z| < Re z`), forward invariant, on which the orbits of `N`
  converge to `0`, carrying an injective holomorphic Fatou coordinate `φa` with
  `φa (N z) = φa z + 1` whose image contains the tail of every horizontal strip.
-/
import Submission.Work.FatouDeg.Petal.petalGeomDefs
import Submission.Work.FatouDeg.Petal.polyAlgebraAux
import Submission.Work.FatouDeg.Petal.fatouCoordSec3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

