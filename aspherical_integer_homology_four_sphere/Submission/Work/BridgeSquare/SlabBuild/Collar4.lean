import Mathlib
import Submission.Work.BridgeSquare.SlabBuild.Infra

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.SlabBuild

open Convexity
open Work.Subdivision
open Work.MbarHomology
open Work.BridgeSquare.WallCollar

noncomputable section

-- The `ℤ`-action on the chain modules is reached through `ZSMul.toSMul`; making that instance the
-- preferred one lets `map_smul`/`smul_smul`/`smul_zero` fire (the device of `PlaneAff.lean`).
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

/-! ## The collar identity of cusp `4`

`D1`..`D5`  are the coefficient tables of the five pieces of the identity
`dLC 1 collarChain4 = dLC 1 wallChain4 - dLC 1 slabBot`, indexed by the *atoms* (the
directed edges) `B4`, and `aC4`..`aB41` are the atom of each slot of each piece.  The
identity is then the pointwise identity of the coefficients `D1 - D2 = D3 - (D4 - D5)`.
-/

/-- The number of distinct atoms of the collar identity of cusp `4`. -/
abbrev Nat4 : ℕ := 322
/-- The atoms (directed edges) of the collar identity of cusp `4`. -/
def B4 : Fin Nat4 → (Fin 2 → CuspE3) :=
  ![![slabPt (-1/2) (-1/8) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-1/2) (-1/8) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (-1/2) (-7/8) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (-3/8) (-7/8) 1],
    ![slabPt (-1/2) (-3/4) 1, slabPt (-5/8) (-7/8) 1],
    ![slabPt (-1/2) (-3/8) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/2) (-3/8) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-1/2) (-5/8) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-1/2) (-5/8) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-1/2) (-7/8) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-1/2) (-7/8) 1, slabPt (-3/8) (-7/8) 1],
    ![slabPt (-1/2) (-7/8) 1, slabPt (-5/8) (-7/8) 1],
    ![slabPt (-1/2) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/8) 1],
    ![slabPt (-1/2) (1/4) 1, slabPt (-3/8) (1/8) 1],
    ![slabPt (-1/2) (1/4) 1, slabPt (-5/8) (1/8) 1],
    ![slabPt (-1/2) (1/8) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-1/2) (1/8) 1, slabPt (-3/8) (1/8) 1],
    ![slabPt (-1/2) (1/8) 1, slabPt (-5/8) (1/8) 1],
    ![slabPt (-1/2) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (-1/4) (-7/8) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (-1/8) (-7/8) 1],
    ![slabPt (-1/4) (-3/4) 1, slabPt (-3/8) (-7/8) 1],
    ![slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-1/4) (-5/8) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/4) (-5/8) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/4) (-7/8) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/4) (-7/8) 1, slabPt (-1/8) (-7/8) 1],
    ![slabPt (-1/4) (-7/8) 1, slabPt (-3/8) (-7/8) 1],
    ![slabPt (-1/4) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/8) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (-1/8) (1/8) 1],
    ![slabPt (-1/4) (1/4) 1, slabPt (-3/8) (1/8) 1],
    ![slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/4) (1/8) 1, slabPt (-1/8) (1/8) 1],
    ![slabPt (-1/4) (1/8) 1, slabPt (-3/8) (1/8) 1],
    ![slabPt (-1/4) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (-1/8) (-1/2) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/8) (-1/2) 1, slabPt (0) (-1/2) 1],
    ![slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/4) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1],
    ![slabPt (-1/8) (-1/8) 1, slabPt (0) (0) 1],
    ![slabPt (-1/8) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/8) (-3/4) 1, slabPt (0) (-3/4) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/2) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (0) (-1/2) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (0) (-1/4) 1],
    ![slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (-1/4) (-5/8) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (-1/8) (-1/2) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (-1/8) (-3/4) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (0) (-1/2) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (0) (-3/4) 1],
    ![slabPt (-1/8) (-5/8) 1, slabPt (0) (-5/8) 1],
    ![slabPt (-1/8) (-7/8) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-1/8) (-7/8) 1, slabPt (-1/4) (-7/8) 1],
    ![slabPt (-1/8) (-7/8) 1, slabPt (-1/8) (-3/4) 1],
    ![slabPt (-1/8) (-7/8) 1, slabPt (0) (-3/4) 1],
    ![slabPt (-1/8) (-7/8) 1, slabPt (0) (-7/8) 1],
    ![slabPt (-1/8) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-1/8) (-7/8) 1, slabPt (1/8) (-7/8) 1],
    ![slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/8) (0) 1, slabPt (0) (0) 1],
    ![slabPt (-1/8) (1/8) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1],
    ![slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1],
    ![slabPt (-1/8) (1/8) 1, slabPt (0) (0) 1],
    ![slabPt (-1/8) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1],
    ![slabPt (-1/8) (1/8) 1, slabPt (1/8) (1/8) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-1/2) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-3/8) 1],
    ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-5/8) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-1/4) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-1/8) 1],
    ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-3/8) 1],
    ![slabPt (-3/4) (-1/8) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-3/4) (-1/8) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-7/8) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-5/8) (-7/8) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-3/4) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-5/8) 1],
    ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-7/8) 1],
    ![slabPt (-3/4) (-3/8) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-3/4) (-3/8) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-3/4) (-5/8) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-3/4) (-5/8) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-3/4) (-7/8) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-3/4) (-7/8) 1, slabPt (-5/8) (-7/8) 1],
    ![slabPt (-3/4) (-7/8) 1, slabPt (-7/8) (-7/8) 1],
    ![slabPt (-3/4) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-3/4) (0) 1, slabPt (-7/8) (0) 1],
    ![slabPt (-3/4) (0) 1, slabPt (-7/8) (1/8) 1],
    ![slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/8) 1],
    ![slabPt (-3/4) (1/4) 1, slabPt (-5/8) (1/8) 1],
    ![slabPt (-3/4) (1/4) 1, slabPt (-7/8) (1/8) 1],
    ![slabPt (-3/4) (1/8) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-3/4) (1/8) 1, slabPt (-5/8) (1/8) 1],
    ![slabPt (-3/4) (1/8) 1, slabPt (-7/8) (1/8) 1],
    ![slabPt (-3/4) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (-3/8) (-1/2) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-3/8) (-1/2) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-3/8) (-1/4) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-1/2) (-1/8) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1],
    ![slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1],
    ![slabPt (-3/8) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-3/8) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-1/2) (-3/8) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-1/4) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/2) 1],
    ![slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-1/2) (-5/8) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-1/4) (-1/2) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-1/4) (-5/8) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-3/8) (-1/2) 1],
    ![slabPt (-3/8) (-5/8) 1, slabPt (-3/8) (-3/4) 1],
    ![slabPt (-3/8) (-7/8) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-3/8) (-7/8) 1, slabPt (-1/2) (-7/8) 1],
    ![slabPt (-3/8) (-7/8) 1, slabPt (-1/4) (-3/4) 1],
    ![slabPt (-3/8) (-7/8) 1, slabPt (-1/4) (-7/8) 1],
    ![slabPt (-3/8) (-7/8) 1, slabPt (-3/8) (-3/4) 1],
    ![slabPt (-3/8) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-3/8) (0) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-3/8) (1/8) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-3/8) (1/8) 1, slabPt (-1/2) (1/8) 1],
    ![slabPt (-3/8) (1/8) 1, slabPt (-1/4) (0) 1],
    ![slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1],
    ![slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1],
    ![slabPt (-3/8) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (-5/8) (-1/2) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-5/8) (-1/2) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-5/8) (-1/4) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-5/8) (-1/4) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-1/2) (-1/8) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-3/4) (-1/8) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-5/8) (-1/4) 1],
    ![slabPt (-5/8) (-1/8) 1, slabPt (-5/8) (0) 1],
    ![slabPt (-5/8) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-5/8) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-1/2) (-1/4) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-1/2) (-3/8) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-3/4) (-3/8) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-5/8) (-1/2) 1],
    ![slabPt (-5/8) (-3/8) 1, slabPt (-5/8) (-1/4) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-1/2) (-1/2) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-1/2) (-5/8) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-3/4) (-5/8) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-5/8) (-1/2) 1],
    ![slabPt (-5/8) (-5/8) 1, slabPt (-5/8) (-3/4) 1],
    ![slabPt (-5/8) (-7/8) 1, slabPt (-1/2) (-3/4) 1],
    ![slabPt (-5/8) (-7/8) 1, slabPt (-1/2) (-7/8) 1],
    ![slabPt (-5/8) (-7/8) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-5/8) (-7/8) 1, slabPt (-3/4) (-7/8) 1],
    ![slabPt (-5/8) (-7/8) 1, slabPt (-5/8) (-3/4) 1],
    ![slabPt (-5/8) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-5/8) (0) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-5/8) (0) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-5/8) (1/8) 1, slabPt (-1/2) (0) 1],
    ![slabPt (-5/8) (1/8) 1, slabPt (-1/2) (1/8) 1],
    ![slabPt (-5/8) (1/8) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-5/8) (1/8) 1, slabPt (-3/4) (1/8) 1],
    ![slabPt (-5/8) (1/8) 1, slabPt (-5/8) (0) 1],
    ![slabPt (-5/8) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (-7/8) (-1/2) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-7/8) (-1/2) 1, slabPt (-7/8) (-3/8) 1],
    ![slabPt (-7/8) (-1/2) 1, slabPt (-7/8) (-5/8) 1],
    ![slabPt (-7/8) (-1/2) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (-1/4) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-7/8) (-1/4) 1, slabPt (-7/8) (-1/8) 1],
    ![slabPt (-7/8) (-1/4) 1, slabPt (-7/8) (-3/8) 1],
    ![slabPt (-7/8) (-1/4) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (-1/8) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-7/8) (-1/8) 1, slabPt (-3/4) (-1/8) 1],
    ![slabPt (-7/8) (-1/8) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-7/8) (-1/8) 1, slabPt (-7/8) (-1/4) 1],
    ![slabPt (-7/8) (-1/8) 1, slabPt (-7/8) (0) 1],
    ![slabPt (-7/8) (-1/8) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-7/8) (-3/4) 1, slabPt (-7/8) (-5/8) 1],
    ![slabPt (-7/8) (-3/4) 1, slabPt (-7/8) (-7/8) 1],
    ![slabPt (-7/8) (-3/4) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (-3/8) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-7/8) (-3/8) 1, slabPt (-3/4) (-1/4) 1],
    ![slabPt (-7/8) (-3/8) 1, slabPt (-3/4) (-3/8) 1],
    ![slabPt (-7/8) (-3/8) 1, slabPt (-7/8) (-1/2) 1],
    ![slabPt (-7/8) (-3/8) 1, slabPt (-7/8) (-1/4) 1],
    ![slabPt (-7/8) (-3/8) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (-5/8) 1, slabPt (-3/4) (-1/2) 1],
    ![slabPt (-7/8) (-5/8) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-7/8) (-5/8) 1, slabPt (-3/4) (-5/8) 1],
    ![slabPt (-7/8) (-5/8) 1, slabPt (-7/8) (-1/2) 1],
    ![slabPt (-7/8) (-5/8) 1, slabPt (-7/8) (-3/4) 1],
    ![slabPt (-7/8) (-5/8) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (-7/8) 1, slabPt (-3/4) (-3/4) 1],
    ![slabPt (-7/8) (-7/8) 1, slabPt (-3/4) (-7/8) 1],
    ![slabPt (-7/8) (-7/8) 1, slabPt (-7/8) (-3/4) 1],
    ![slabPt (-7/8) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (0) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-7/8) (0) 1, slabPt (-7/8) (1/8) 1],
    ![slabPt (-7/8) (0) 1, slabPt (0) (0) 0],
    ![slabPt (-7/8) (1/8) 1, slabPt (-3/4) (0) 1],
    ![slabPt (-7/8) (1/8) 1, slabPt (-3/4) (1/8) 1],
    ![slabPt (-7/8) (1/8) 1, slabPt (-7/8) (0) 1],
    ![slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1],
    ![slabPt (0) (-1/8) 1, slabPt (0) (0) 1],
    ![slabPt (0) (-3/8) 1, slabPt (0) (-1/2) 1],
    ![slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1],
    ![slabPt (0) (-5/8) 1, slabPt (0) (-1/2) 1],
    ![slabPt (0) (-5/8) 1, slabPt (0) (-3/4) 1],
    ![slabPt (0) (-7/8) 1, slabPt (0) (-3/4) 1],
    ![slabPt (0) (-7/8) 1, slabPt (0) (0) 0],
    ![slabPt (0) (-7/8) 1, slabPt (1/8) (-7/8) 1],
    ![slabPt (0) (0) 0, slabPt (-7/8) (-7/8) 1],
    ![slabPt (0) (0) 0, slabPt (-7/8) (1/8) 1],
    ![slabPt (0) (0) 0, slabPt (0) (1) 0],
    ![slabPt (0) (0) 0, slabPt (1) (0) 0],
    ![slabPt (0) (0) 0, slabPt (1) (1) 0],
    ![slabPt (0) (0) 0, slabPt (1/8) (-7/8) 1],
    ![slabPt (0) (1) 0, slabPt (-7/8) (1/8) 1],
    ![slabPt (0) (1) 0, slabPt (1) (1) 0],
    ![slabPt (0) (1) 0, slabPt (1/8) (1/8) 1],
    ![slabPt (0) (1/8) 1, slabPt (0) (0) 1],
    ![slabPt (0) (1/8) 1, slabPt (0) (1) 0],
    ![slabPt (0) (1/8) 1, slabPt (1/8) (1/8) 1],
    ![slabPt (1) (0) 0, slabPt (1) (1) 0],
    ![slabPt (1) (0) 0, slabPt (1/8) (-7/8) 1],
    ![slabPt (1) (0) 0, slabPt (1/8) (1/8) 1],
    ![slabPt (1) (1) 0, slabPt (1/8) (1/8) 1],
    ![slabPt (1/4) (-1/2) 1, slabPt (1/8) (-1/2) 1],
    ![slabPt (1/4) (-1/2) 1, slabPt (1/8) (-3/8) 1],
    ![slabPt (1/4) (-1/2) 1, slabPt (1/8) (-5/8) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (1/8) (-1/4) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (1/8) (-1/8) 1],
    ![slabPt (1/4) (-1/4) 1, slabPt (1/8) (-3/8) 1],
    ![slabPt (1/4) (-3/4) 1, slabPt (1/8) (-3/4) 1],
    ![slabPt (1/4) (-3/4) 1, slabPt (1/8) (-5/8) 1],
    ![slabPt (1/4) (-3/4) 1, slabPt (1/8) (-7/8) 1],
    ![slabPt (1/4) (-7/8) 1, slabPt (1) (0) 0],
    ![slabPt (1/4) (-7/8) 1, slabPt (1/8) (-7/8) 1],
    ![slabPt (1/4) (0) 1, slabPt (1/8) (0) 1],
    ![slabPt (1/4) (0) 1, slabPt (1/8) (1/8) 1],
    ![slabPt (1/8) (-1/2) 1, slabPt (0) (-1/2) 1],
    ![slabPt (1/8) (-1/2) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-1/2) 1, slabPt (1/8) (-3/8) 1],
    ![slabPt (1/8) (-1/2) 1, slabPt (1/8) (-5/8) 1],
    ![slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1],
    ![slabPt (1/8) (-1/4) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-1/4) 1, slabPt (1/8) (-1/8) 1],
    ![slabPt (1/8) (-1/4) 1, slabPt (1/8) (-3/8) 1],
    ![slabPt (1/8) (-1/8) 1, slabPt (0) (-1/4) 1],
    ![slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1],
    ![slabPt (1/8) (-1/8) 1, slabPt (0) (0) 1],
    ![slabPt (1/8) (-1/8) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1],
    ![slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1],
    ![slabPt (1/8) (-3/4) 1, slabPt (0) (-3/4) 1],
    ![slabPt (1/8) (-3/4) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-3/4) 1, slabPt (1/8) (-5/8) 1],
    ![slabPt (1/8) (-3/4) 1, slabPt (1/8) (-7/8) 1],
    ![slabPt (1/8) (-3/8) 1, slabPt (0) (-1/2) 1],
    ![slabPt (1/8) (-3/8) 1, slabPt (0) (-1/4) 1],
    ![slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1],
    ![slabPt (1/8) (-3/8) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/2) 1],
    ![slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1],
    ![slabPt (1/8) (-5/8) 1, slabPt (0) (-1/2) 1],
    ![slabPt (1/8) (-5/8) 1, slabPt (0) (-3/4) 1],
    ![slabPt (1/8) (-5/8) 1, slabPt (0) (-5/8) 1],
    ![slabPt (1/8) (-5/8) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-5/8) 1, slabPt (1/8) (-1/2) 1],
    ![slabPt (1/8) (-5/8) 1, slabPt (1/8) (-3/4) 1],
    ![slabPt (1/8) (-7/8) 1, slabPt (0) (-3/4) 1],
    ![slabPt (1/8) (-7/8) 1, slabPt (0) (-7/8) 1],
    ![slabPt (1/8) (-7/8) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (-7/8) 1, slabPt (1/8) (-3/4) 1],
    ![slabPt (1/8) (0) 1, slabPt (0) (0) 1],
    ![slabPt (1/8) (0) 1, slabPt (1) (0) 0],
    ![slabPt (1/8) (0) 1, slabPt (1/8) (1/8) 1],
    ![slabPt (1/8) (1/8) 1, slabPt (0) (0) 1],
    ![slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1],
    ![slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1]]

/-- The flat index of a `(j,i)` slot. -/
def fl4 (p : Fin 48 × Fin 3) : Fin (3 * 48) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩
/-- The flat index of a `(j,i)` slot of the wall. -/
def flw4 (p : Fin 128 × Fin 3) : Fin (3 * 128) :=
  ⟨3 * (p.1 : ℕ) + (p.2 : ℕ), by have h := p.1.isLt; have h2 := p.2.isLt; omega⟩

def aCF4 : Fin (3 * 48) → Fin Nat4 := ![10, 3, 2, 11, 4, 2, 147, 2, 3, 191, 2, 4, 151, 12, 10, 195, 12, 11, 30, 23, 22, 31, 24, 22, 71, 22, 23, 149, 22, 24, 75, 32, 30, 151, 32, 31, 251, 75, 74, 252, 76, 74, 313, 74, 76, 205, 87, 86, 206, 88, 86, 225, 86, 87, 231, 86, 88, 209, 90, 89, 210, 91, 89, 215, 89, 90, 226, 89, 91, 104, 95, 94, 105, 98, 94, 193, 94, 95, 219, 97, 96, 220, 98, 96, 232, 96, 97, 235, 94, 98, 236, 96, 98, 195, 106, 104, 237, 106, 105, 253, 105, 106, 253, 105, 106, 239, 108, 107, 243, 107, 108, 227, 207, 205, 233, 207, 206, 217, 211, 209, 227, 211, 210, 240, 217, 216, 233, 221, 219, 237, 221, 220, 254, 239, 240, 258, 252, 251, 259, 254, 255, 266, 258, 256]
def aCF4' : Fin (3 * 48) → Fin Nat4 := ![17, 14, 13, 18, 15, 13, 155, 13, 14, 199, 13, 15, 159, 19, 17, 203, 19, 18, 37, 34, 33, 38, 35, 33, 80, 33, 34, 157, 33, 35, 83, 39, 37, 159, 39, 38, 263, 83, 84, 264, 85, 84, 320, 84, 85, 284, 270, 269, 285, 271, 269, 304, 269, 270, 310, 269, 271, 288, 273, 272, 289, 274, 272, 294, 272, 273, 305, 272, 274, 113, 110, 109, 114, 111, 109, 201, 109, 110, 298, 276, 275, 299, 277, 275, 311, 275, 276, 242, 109, 111, 315, 275, 277, 203, 115, 113, 314, 278, 279, 266, 279, 278, 259, 114, 115, 318, 281, 280, 321, 280, 281, 303, 283, 284, 309, 283, 285, 293, 287, 288, 303, 287, 289, 317, 293, 295, 309, 297, 298, 314, 297, 299, 267, 318, 317, 261, 264, 263, 268, 267, 265, 268, 261, 260]
def aWF4 : Fin (3 * 128) → Fin Nat4 := ![262, 319, 320, 262, 82, 84, 316, 319, 321, 316, 292, 295, 78, 51, 48, 78, 82, 81, 245, 51, 50, 245, 292, 291, 250, 312, 313, 250, 73, 74, 296, 312, 315, 296, 307, 311, 53, 68, 66, 53, 73, 72, 249, 68, 69, 249, 307, 308, 112, 241, 242, 112, 200, 201, 238, 241, 243, 238, 214, 216, 197, 169, 171, 197, 200, 202, 93, 169, 168, 93, 214, 213, 36, 156, 157, 36, 79, 80, 153, 156, 158, 153, 125, 127, 77, 46, 48, 77, 79, 81, 21, 46, 45, 21, 125, 124, 247, 301, 302, 247, 60, 61, 286, 301, 305, 286, 290, 294, 43, 49, 47, 43, 60, 58, 244, 49, 50, 244, 290, 291, 103, 234, 235, 103, 192, 193, 218, 234, 236, 218, 229, 232, 173, 186, 189, 173, 192, 194, 102, 186, 187, 102, 229, 230, 29, 148, 149, 29, 70, 71, 129, 148, 150, 129, 142, 145, 52, 63, 66, 52, 70, 72, 28, 63, 64, 28, 142, 143, 246, 300, 302, 246, 59, 61, 282, 300, 304, 282, 306, 310, 41, 67, 65, 41, 59, 57, 248, 67, 69, 248, 306, 308, 16, 154, 155, 16, 198, 199, 152, 154, 158, 152, 122, 127, 196, 166, 171, 196, 198, 202, 1, 166, 165, 1, 122, 121, 100, 223, 224, 100, 178, 179, 208, 223, 226, 208, 212, 215, 163, 167, 170, 163, 178, 181, 92, 167, 168, 92, 212, 213, 26, 134, 135, 26, 55, 56, 119, 134, 137, 119, 123, 126, 42, 44, 47, 42, 55, 58, 20, 44, 45, 20, 123, 124, 9, 146, 147, 9, 190, 191, 128, 146, 150, 128, 139, 145, 172, 183, 189, 172, 190, 194, 8, 183, 184, 8, 139, 140, 99, 222, 224, 99, 177, 179, 204, 222, 225, 204, 228, 231, 161, 185, 188, 161, 177, 180, 101, 185, 187, 101, 228, 230, 25, 133, 135, 25, 54, 56, 117, 133, 136, 117, 141, 144, 40, 62, 65, 40, 54, 57, 27, 62, 64, 27, 141, 143, 6, 131, 132, 6, 175, 176, 118, 131, 137, 118, 120, 126, 162, 164, 170, 162, 175, 181, 0, 164, 165, 0, 120, 121, 5, 130, 132, 5, 174, 176, 116, 130, 136, 116, 138, 144, 160, 182, 188, 160, 174, 180, 7, 182, 184, 7, 138, 140]
def aB40 : Fin 3 → Fin Nat4 := ![265, 257, 256]
def aB41 : Fin 3 → Fin Nat4 := ![260, 257, 255]

/-- The atom of the first edge family of the collar. -/
def aC4 : Fin 48 × Fin 3 → Fin Nat4 := fun p => aCF4 (fl4 p)
/-- The atom of the second edge family of the collar. -/
def aC4' : Fin 48 × Fin 3 → Fin Nat4 := fun p => aCF4' (fl4 p)
/-- The atom of the edges of the wall. -/
def aW4 : Fin 128 × Fin 3 → Fin Nat4 := fun p => aWF4 (flw4 p)

def cC4 : Fin 48 × Fin 3 → ℤ := fun p => colCoef4 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cC4' : Fin 48 × Fin 3 → ℤ := fun p => colCoef4 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cW4 : Fin 128 × Fin 3 → ℤ := fun p => coefV4 p.1 * ((-1 : ℤ) ^ (p.2 : ℕ))
def cB4 : Fin 3 → ℤ := fun i => ((-1 : ℤ) ^ (i : ℕ))

def D14 : Fin Nat4 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC4 p = l), cC4 p
def D24 : Fin Nat4 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aC4' p = l), cC4' p
def D34 : Fin Nat4 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aW4 p = l), cW4 p
def D44 : Fin Nat4 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB40 p = l), cB4 p
def D54 : Fin Nat4 → ℤ := fun l =>
  ∑ p ∈ Finset.univ.filter (fun p => aB41 p = l), cB4 p

/-- The canonical basis vector of each atom. -/
abbrev X4 : Fin Nat4 → AffC 1 := fun l => Finsupp.single (B4 l) (1 : ℤ)

set_option maxHeartbeats 0 in
/-- The pointwise coefficient identity of the collar of cusp `4`. -/
theorem hcoef4 : ∀ l : Fin Nat4, D14 l - D24 l = D34 l - (D44 l - D54 l) := by
  decide

/-- The atoms of the first edge family of the collar. -/
theorem brC4 : ∀ p : Fin 48 × Fin 3, B4 (aC4 p) = vface (k := 1) p.2 (colTri4 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j <;> fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem cS4_0 : (fun k => colTri4 0 k + colLam4 0) = ![slabPt (-1/2) (1/4) (1), slabPt (-1/2) (1/8) (1), slabPt (-3/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_1 : (fun k => colTri4 1 k + colLam4 1) = ![slabPt (-1/2) (1/4) (1), slabPt (-1/2) (1/8) (1), slabPt (-5/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-5/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_2 : (fun k => colTri4 2 k + colLam4 2) = ![slabPt (-1/2) (1/4) (1), slabPt (-3/8) (1/8) (1), slabPt (-1/2) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_3 : (fun k => colTri4 3 k + colLam4 3) = ![slabPt (-1/2) (1/4) (1), slabPt (-5/8) (1/8) (1), slabPt (-1/2) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-5/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/2) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_4 : (fun k => colTri4 4 k + colLam4 4) = ![slabPt (-1/2) (1/8) (1), slabPt (-3/8) (1/8) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS4_5 : (fun k => colTri4 5 k + colLam4 5) = ![slabPt (-1/2) (1/8) (1), slabPt (-5/8) (1/8) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/2) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-5/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS4_6 : (fun k => colTri4 6 k + colLam4 6) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (1/8) (1), slabPt (-1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_7 : (fun k => colTri4 7 k + colLam4 7) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/4) (1/8) (1), slabPt (-3/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_8 : (fun k => colTri4 8 k + colLam4 8) = ![slabPt (-1/4) (1/4) (1), slabPt (-1/8) (1/8) (1), slabPt (-1/4) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_9 : (fun k => colTri4 9 k + colLam4 9) = ![slabPt (-1/4) (1/4) (1), slabPt (-3/8) (1/8) (1), slabPt (-1/4) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_10 : (fun k => colTri4 10 k + colLam4 10) = ![slabPt (-1/4) (1/8) (1), slabPt (-1/8) (1/8) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS4_11 : (fun k => colTri4 11 k + colLam4 11) = ![slabPt (-1/4) (1/8) (1), slabPt (-3/8) (1/8) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS4_12 : (fun k => colTri4 12 k + colLam4 12) = ![slabPt (-1/8) (1/8) (1), slabPt (0) (1/8) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS4_13 : (fun k => colTri4 13 k + colLam4 13) = ![slabPt (-1/8) (1/8) (1), slabPt (0) (1/8) (1), slabPt (1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_14 : (fun k => colTri4 14 k + colLam4 14) = ![slabPt (-1/8) (1/8) (1), slabPt (1/8) (1/8) (1), slabPt (0) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_15 : (fun k => colTri4 15 k + colLam4 15) = ![slabPt (1/4) (-1/2) (1), slabPt (1/8) (-1/2) (1), slabPt (1/8) (-3/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_16 : (fun k => colTri4 16 k + colLam4 16) = ![slabPt (1/4) (-1/2) (1), slabPt (1/8) (-1/2) (1), slabPt (1/8) (-5/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-5/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_17 : (fun k => colTri4 17 k + colLam4 17) = ![slabPt (1/4) (-1/2) (1), slabPt (1/8) (-3/8) (1), slabPt (1/8) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS4_18 : (fun k => colTri4 18 k + colLam4 18) = ![slabPt (1/4) (-1/2) (1), slabPt (1/8) (-5/8) (1), slabPt (1/8) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-5/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem cS4_19 : (fun k => colTri4 19 k + colLam4 19) = ![slabPt (1/4) (-1/4) (1), slabPt (1/8) (-1/4) (1), slabPt (1/8) (-1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_20 : (fun k => colTri4 20 k + colLam4 20) = ![slabPt (1/4) (-1/4) (1), slabPt (1/8) (-1/4) (1), slabPt (1/8) (-3/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_21 : (fun k => colTri4 21 k + colLam4 21) = ![slabPt (1/4) (-1/4) (1), slabPt (1/8) (-1/8) (1), slabPt (1/8) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS4_22 : (fun k => colTri4 22 k + colLam4 22) = ![slabPt (1/4) (-1/4) (1), slabPt (1/8) (-3/8) (1), slabPt (1/8) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem cS4_23 : (fun k => colTri4 23 k + colLam4 23) = ![slabPt (-3/4) (1/4) (1), slabPt (-3/4) (1/8) (1), slabPt (-5/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-5/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_24 : (fun k => colTri4 24 k + colLam4 24) = ![slabPt (-3/4) (1/4) (1), slabPt (-3/4) (1/8) (1), slabPt (-7/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_25 : (fun k => colTri4 25 k + colLam4 25) = ![slabPt (-3/4) (1/4) (1), slabPt (-5/8) (1/8) (1), slabPt (-3/4) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-5/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_26 : (fun k => colTri4 26 k + colLam4 26) = ![slabPt (1/4) (-3/4) (1), slabPt (1/8) (-3/4) (1), slabPt (1/8) (-5/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-5/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_27 : (fun k => colTri4 27 k + colLam4 27) = ![slabPt (1/4) (-3/4) (1), slabPt (1/8) (-3/4) (1), slabPt (1/8) (-7/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_28 : (fun k => colTri4 28 k + colLam4 28) = ![slabPt (1/4) (-3/4) (1), slabPt (1/8) (-5/8) (1), slabPt (1/8) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-5/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS4_29 : (fun k => colTri4 29 k + colLam4 29) = ![slabPt (-3/4) (1/4) (1), slabPt (-7/8) (1/8) (1), slabPt (-3/4) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_30 : (fun k => colTri4 30 k + colLam4 30) = ![slabPt (1/4) (-3/4) (1), slabPt (1/8) (-7/8) (1), slabPt (1/8) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem cS4_31 : (fun k => colTri4 31 k + colLam4 31) = ![slabPt (-3/4) (1/8) (1), slabPt (-5/8) (1/8) (1), slabPt (0) (1) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-5/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num

theorem cS4_32 : (fun k => colTri4 32 k + colLam4 32) = ![slabPt (1/4) (-7/8) (1), slabPt (1/8) (-7/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_33 : (fun k => colTri4 33 k + colLam4 33) = ![slabPt (1/4) (-7/8) (1), slabPt (1) (0) (0), slabPt (1/8) (-7/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_34 : (fun k => colTri4 34 k + colLam4 34) = ![slabPt (-3/4) (1/8) (1), slabPt (0) (1) (0), slabPt (-7/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_35 : (fun k => colTri4 35 k + colLam4 35) = ![slabPt (1/4) (0) (1), slabPt (1/8) (0) (1), slabPt (1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (0) (1) + slabPt (1) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_36 : (fun k => colTri4 36 k + colLam4 36) = ![slabPt (1/4) (0) (1), slabPt (1/8) (1/8) (1), slabPt (1/8) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/4) (0) (1) + slabPt (1) (0) (0) = slabPt (1/4) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (0) (1) + slabPt (1) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num

theorem cS4_37 : (fun k => colTri4 37 k + colLam4 37) = ![slabPt (1/8) (-1/2) (1), slabPt (1/8) (-3/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_38 : (fun k => colTri4 38 k + colLam4 38) = ![slabPt (1/8) (-1/2) (1), slabPt (1/8) (-5/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-1/2) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-5/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_39 : (fun k => colTri4 39 k + colLam4 39) = ![slabPt (1/8) (-1/4) (1), slabPt (1/8) (-1/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_40 : (fun k => colTri4 40 k + colLam4 40) = ![slabPt (1/8) (-1/4) (1), slabPt (1/8) (-3/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-1/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-3/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_41 : (fun k => colTri4 41 k + colLam4 41) = ![slabPt (1/8) (-1/8) (1), slabPt (1/8) (0) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (0) (1) + slabPt (1) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_42 : (fun k => colTri4 42 k + colLam4 42) = ![slabPt (1/8) (-3/4) (1), slabPt (1/8) (-5/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-5/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_43 : (fun k => colTri4 43 k + colLam4 43) = ![slabPt (1/8) (-3/4) (1), slabPt (1/8) (-7/8) (1), slabPt (1) (0) (0)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (-3/4) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (-7/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num

theorem cS4_44 : (fun k => colTri4 44 k + colLam4 44) = ![slabPt (1/8) (0) (1), slabPt (1) (0) (0), slabPt (1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-7/8) (0) (1) + slabPt (1) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_45 : (fun k => colTri4 45 k + colLam4 45) = ![slabPt (0) (1/8) (1), slabPt (0) (1) (0), slabPt (1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_46 : (fun k => colTri4 46 k + colLam4 46) = ![slabPt (1) (0) (0), slabPt (1) (1) (0), slabPt (1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (1) (0) (0) = slabPt (1) (0) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1) (0) + slabPt (1) (0) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (-7/8) (1/8) (1) + slabPt (1) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem cS4_47 : (fun k => colTri4 47 k + colLam4 47) = ![slabPt (0) (1) (0), slabPt (1) (1) (0), slabPt (1/8) (1/8) (1)] := by
  funext k
  fin_cases k
  · show slabPt (0) (0) (0) + slabPt (0) (1) (0) = slabPt (0) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1) (0) (0) + slabPt (0) (1) (0) = slabPt (1) (1) (0)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-7/8) (1) + slabPt (0) (1) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num

theorem tS4_0 : (fun k => tauV4 0 k + lamV4 0) = ![slabPt (1/8) (1/8) (1), slabPt (0) (1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_1 : (fun k => tauV4 1 k + lamV4 1) = ![slabPt (-1/8) (1/8) (1), slabPt (0) (1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_2 : (fun k => tauV4 2 k + lamV4 2) = ![slabPt (1/8) (1/8) (1), slabPt (1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_3 : (fun k => tauV4 3 k + lamV4 3) = ![slabPt (1/8) (-1/8) (1), slabPt (1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_4 : (fun k => tauV4 4 k + lamV4 4) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_5 : (fun k => tauV4 5 k + lamV4 5) = ![slabPt (-1/8) (1/8) (1), slabPt (-1/8) (0) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_6 : (fun k => tauV4 6 k + lamV4 6) = ![slabPt (-1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_7 : (fun k => tauV4 7 k + lamV4 7) = ![slabPt (1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (0) (1) + slabPt (0) (0) (0) = slabPt (0) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_8 : (fun k => tauV4 8 k + lamV4 8) = ![slabPt (1/8) (-7/8) (1), slabPt (0) (-7/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_9 : (fun k => tauV4 9 k + lamV4 9) = ![slabPt (-1/8) (-7/8) (1), slabPt (0) (-7/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_10 : (fun k => tauV4 10 k + lamV4 10) = ![slabPt (1/8) (-7/8) (1), slabPt (1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_11 : (fun k => tauV4 11 k + lamV4 11) = ![slabPt (1/8) (-5/8) (1), slabPt (1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_12 : (fun k => tauV4 12 k + lamV4 12) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_13 : (fun k => tauV4 13 k + lamV4 13) = ![slabPt (-1/8) (-7/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_14 : (fun k => tauV4 14 k + lamV4 14) = ![slabPt (-1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_15 : (fun k => tauV4 15 k + lamV4 15) = ![slabPt (1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_16 : (fun k => tauV4 16 k + lamV4 16) = ![slabPt (-7/8) (1/8) (1), slabPt (-3/4) (1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_17 : (fun k => tauV4 17 k + lamV4 17) = ![slabPt (-5/8) (1/8) (1), slabPt (-3/4) (1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_18 : (fun k => tauV4 18 k + lamV4 18) = ![slabPt (-7/8) (1/8) (1), slabPt (-7/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_19 : (fun k => tauV4 19 k + lamV4 19) = ![slabPt (-7/8) (-1/8) (1), slabPt (-7/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_20 : (fun k => tauV4 20 k + lamV4 20) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_21 : (fun k => tauV4 21 k + lamV4 21) = ![slabPt (-5/8) (1/8) (1), slabPt (-5/8) (0) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_22 : (fun k => tauV4 22 k + lamV4 22) = ![slabPt (-5/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_23 : (fun k => tauV4 23 k + lamV4 23) = ![slabPt (-7/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_24 : (fun k => tauV4 24 k + lamV4 24) = ![slabPt (-3/8) (1/8) (1), slabPt (-1/4) (1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_25 : (fun k => tauV4 25 k + lamV4 25) = ![slabPt (-1/8) (1/8) (1), slabPt (-1/4) (1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_26 : (fun k => tauV4 26 k + lamV4 26) = ![slabPt (-3/8) (1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_27 : (fun k => tauV4 27 k + lamV4 27) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_28 : (fun k => tauV4 28 k + lamV4 28) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_29 : (fun k => tauV4 29 k + lamV4 29) = ![slabPt (-1/8) (1/8) (1), slabPt (-1/8) (0) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_30 : (fun k => tauV4 30 k + lamV4 30) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_31 : (fun k => tauV4 31 k + lamV4 31) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (0) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_32 : (fun k => tauV4 32 k + lamV4 32) = ![slabPt (1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_33 : (fun k => tauV4 33 k + lamV4 33) = ![slabPt (-1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_34 : (fun k => tauV4 34 k + lamV4 34) = ![slabPt (1/8) (-3/8) (1), slabPt (1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_35 : (fun k => tauV4 35 k + lamV4 35) = ![slabPt (1/8) (-1/8) (1), slabPt (1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_36 : (fun k => tauV4 36 k + lamV4 36) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_37 : (fun k => tauV4 37 k + lamV4 37) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_38 : (fun k => tauV4 38 k + lamV4 38) = ![slabPt (-1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_39 : (fun k => tauV4 39 k + lamV4 39) = ![slabPt (1/8) (-1/8) (1), slabPt (0) (-1/8) (1), slabPt (0) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (0) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_40 : (fun k => tauV4 40 k + lamV4 40) = ![slabPt (-7/8) (-7/8) (1), slabPt (-3/4) (-7/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_41 : (fun k => tauV4 41 k + lamV4 41) = ![slabPt (-5/8) (-7/8) (1), slabPt (-3/4) (-7/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_42 : (fun k => tauV4 42 k + lamV4 42) = ![slabPt (-7/8) (-7/8) (1), slabPt (-7/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_43 : (fun k => tauV4 43 k + lamV4 43) = ![slabPt (-7/8) (-5/8) (1), slabPt (-7/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_44 : (fun k => tauV4 44 k + lamV4 44) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_45 : (fun k => tauV4 45 k + lamV4 45) = ![slabPt (-5/8) (-7/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_46 : (fun k => tauV4 46 k + lamV4 46) = ![slabPt (-5/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_47 : (fun k => tauV4 47 k + lamV4 47) = ![slabPt (-7/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_48 : (fun k => tauV4 48 k + lamV4 48) = ![slabPt (-3/8) (-7/8) (1), slabPt (-1/4) (-7/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_49 : (fun k => tauV4 49 k + lamV4 49) = ![slabPt (-1/8) (-7/8) (1), slabPt (-1/4) (-7/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_50 : (fun k => tauV4 50 k + lamV4 50) = ![slabPt (-3/8) (-7/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_51 : (fun k => tauV4 51 k + lamV4 51) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_52 : (fun k => tauV4 52 k + lamV4 52) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_53 : (fun k => tauV4 53 k + lamV4 53) = ![slabPt (-1/8) (-7/8) (1), slabPt (-1/8) (-3/4) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (1/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_54 : (fun k => tauV4 54 k + lamV4 54) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_55 : (fun k => tauV4 55 k + lamV4 55) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/4) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_56 : (fun k => tauV4 56 k + lamV4 56) = ![slabPt (1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_57 : (fun k => tauV4 57 k + lamV4 57) = ![slabPt (-1/8) (-3/8) (1), slabPt (0) (-3/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_58 : (fun k => tauV4 58 k + lamV4 58) = ![slabPt (1/8) (-3/8) (1), slabPt (1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_59 : (fun k => tauV4 59 k + lamV4 59) = ![slabPt (1/8) (-5/8) (1), slabPt (1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_60 : (fun k => tauV4 60 k + lamV4 60) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_61 : (fun k => tauV4 61 k + lamV4 61) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_62 : (fun k => tauV4 62 k + lamV4 62) = ![slabPt (-1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_63 : (fun k => tauV4 63 k + lamV4 63) = ![slabPt (1/8) (-5/8) (1), slabPt (0) (-5/8) (1), slabPt (0) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (0) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (0) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (0) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_64 : (fun k => tauV4 64 k + lamV4 64) = ![slabPt (-3/8) (1/8) (1), slabPt (-1/2) (1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_65 : (fun k => tauV4 65 k + lamV4 65) = ![slabPt (-5/8) (1/8) (1), slabPt (-1/2) (1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_66 : (fun k => tauV4 66 k + lamV4 66) = ![slabPt (-3/8) (1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_67 : (fun k => tauV4 67 k + lamV4 67) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_68 : (fun k => tauV4 68 k + lamV4 68) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_69 : (fun k => tauV4 69 k + lamV4 69) = ![slabPt (-5/8) (1/8) (1), slabPt (-5/8) (0) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (0) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (0) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_70 : (fun k => tauV4 70 k + lamV4 70) = ![slabPt (-5/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_71 : (fun k => tauV4 71 k + lamV4 71) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (0) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (0) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (0) (1)
    rw [slabPt_add']; norm_num

theorem tS4_72 : (fun k => tauV4 72 k + lamV4 72) = ![slabPt (-7/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_73 : (fun k => tauV4 73 k + lamV4 73) = ![slabPt (-5/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_74 : (fun k => tauV4 74 k + lamV4 74) = ![slabPt (-7/8) (-3/8) (1), slabPt (-7/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_75 : (fun k => tauV4 75 k + lamV4 75) = ![slabPt (-7/8) (-1/8) (1), slabPt (-7/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_76 : (fun k => tauV4 76 k + lamV4 76) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_77 : (fun k => tauV4 77 k + lamV4 77) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_78 : (fun k => tauV4 78 k + lamV4 78) = ![slabPt (-5/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_79 : (fun k => tauV4 79 k + lamV4 79) = ![slabPt (-7/8) (-1/8) (1), slabPt (-3/4) (-1/8) (1), slabPt (-3/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-7/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_80 : (fun k => tauV4 80 k + lamV4 80) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_81 : (fun k => tauV4 81 k + lamV4 81) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_82 : (fun k => tauV4 82 k + lamV4 82) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_83 : (fun k => tauV4 83 k + lamV4 83) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_84 : (fun k => tauV4 84 k + lamV4 84) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_85 : (fun k => tauV4 85 k + lamV4 85) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/4) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-3/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_86 : (fun k => tauV4 86 k + lamV4 86) = ![slabPt (-1/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_87 : (fun k => tauV4 87 k + lamV4 87) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/4) (-1/8) (1), slabPt (-1/4) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/8) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (-1/4) (1) + slabPt (0) (0) (0) = slabPt (-1/4) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_88 : (fun k => tauV4 88 k + lamV4 88) = ![slabPt (-3/8) (-7/8) (1), slabPt (-1/2) (-7/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_89 : (fun k => tauV4 89 k + lamV4 89) = ![slabPt (-5/8) (-7/8) (1), slabPt (-1/2) (-7/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_90 : (fun k => tauV4 90 k + lamV4 90) = ![slabPt (-3/8) (-7/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_91 : (fun k => tauV4 91 k + lamV4 91) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_92 : (fun k => tauV4 92 k + lamV4 92) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_93 : (fun k => tauV4 93 k + lamV4 93) = ![slabPt (-5/8) (-7/8) (1), slabPt (-5/8) (-3/4) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (1/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-7/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_94 : (fun k => tauV4 94 k + lamV4 94) = ![slabPt (-5/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_95 : (fun k => tauV4 95 k + lamV4 95) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-3/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/4) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_96 : (fun k => tauV4 96 k + lamV4 96) = ![slabPt (-7/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_97 : (fun k => tauV4 97 k + lamV4 97) = ![slabPt (-5/8) (-3/8) (1), slabPt (-3/4) (-3/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_98 : (fun k => tauV4 98 k + lamV4 98) = ![slabPt (-7/8) (-3/8) (1), slabPt (-7/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_99 : (fun k => tauV4 99 k + lamV4 99) = ![slabPt (-7/8) (-5/8) (1), slabPt (-7/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_100 : (fun k => tauV4 100 k + lamV4 100) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_101 : (fun k => tauV4 101 k + lamV4 101) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_102 : (fun k => tauV4 102 k + lamV4 102) = ![slabPt (-5/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_103 : (fun k => tauV4 103 k + lamV4 103) = ![slabPt (-7/8) (-5/8) (1), slabPt (-3/4) (-5/8) (1), slabPt (-3/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (1/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-7/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/4) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_104 : (fun k => tauV4 104 k + lamV4 104) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_105 : (fun k => tauV4 105 k + lamV4 105) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/4) (-3/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_106 : (fun k => tauV4 106 k + lamV4 106) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_107 : (fun k => tauV4 107 k + lamV4 107) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-3/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_108 : (fun k => tauV4 108 k + lamV4 108) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_109 : (fun k => tauV4 109 k + lamV4 109) = ![slabPt (-1/8) (-3/8) (1), slabPt (-1/8) (-1/2) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (5/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/8) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_110 : (fun k => tauV4 110 k + lamV4 110) = ![slabPt (-1/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-1/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_111 : (fun k => tauV4 111 k + lamV4 111) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/4) (-5/8) (1), slabPt (-1/4) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (-3/8) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (3/8) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (-1/4) (1/2) (1) + slabPt (0) (-1) (0) = slabPt (-1/4) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_112 : (fun k => tauV4 112 k + lamV4 112) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_113 : (fun k => tauV4 113 k + lamV4 113) = ![slabPt (-5/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_114 : (fun k => tauV4 114 k + lamV4 114) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_115 : (fun k => tauV4 115 k + lamV4 115) = ![slabPt (-3/8) (-1/8) (1), slabPt (-3/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_116 : (fun k => tauV4 116 k + lamV4 116) = ![slabPt (-5/8) (-1/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_117 : (fun k => tauV4 117 k + lamV4 117) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/4) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-3/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/4) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_118 : (fun k => tauV4 118 k + lamV4 118) = ![slabPt (-5/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-5/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_119 : (fun k => tauV4 119 k + lamV4 119) = ![slabPt (-3/8) (-1/8) (1), slabPt (-1/2) (-1/8) (1), slabPt (-1/2) (-1/4) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-3/8) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/8) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (-1/4) (1) + slabPt (-1) (0) (0) = slabPt (-1/2) (-1/4) (1)
    rw [slabPt_add']; norm_num

theorem tS4_120 : (fun k => tauV4 120 k + lamV4 120) = ![slabPt (-3/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_121 : (fun k => tauV4 121 k + lamV4 121) = ![slabPt (-5/8) (-3/8) (1), slabPt (-1/2) (-3/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_122 : (fun k => tauV4 122 k + lamV4 122) = ![slabPt (-3/8) (-3/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_123 : (fun k => tauV4 123 k + lamV4 123) = ![slabPt (-3/8) (-5/8) (1), slabPt (-3/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (5/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_124 : (fun k => tauV4 124 k + lamV4 124) = ![slabPt (-5/8) (-5/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_125 : (fun k => tauV4 125 k + lamV4 125) = ![slabPt (-5/8) (-3/8) (1), slabPt (-5/8) (-1/2) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (5/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-3/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (3/8) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-1/2) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_126 : (fun k => tauV4 126 k + lamV4 126) = ![slabPt (-5/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (3/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-5/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem tS4_127 : (fun k => tauV4 127 k + lamV4 127) = ![slabPt (-3/8) (-5/8) (1), slabPt (-1/2) (-5/8) (1), slabPt (-1/2) (-1/2) (1)] := by
  funext k
  fin_cases k
  · show slabPt (5/8) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-3/8) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (3/8) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-5/8) (1)
    rw [slabPt_add']; norm_num
  · show slabPt (1/2) (1/2) (1) + slabPt (-1) (-1) (0) = slabPt (-1/2) (-1/2) (1)
    rw [slabPt_add']; norm_num

theorem brC4'_0 (i : Fin 3) : B4 (aC4' (0, i)) = vface (k := 1) i (fun k => colTri4 0 k + colLam4 0) := by
  rw [cS4_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_1 (i : Fin 3) : B4 (aC4' (1, i)) = vface (k := 1) i (fun k => colTri4 1 k + colLam4 1) := by
  rw [cS4_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_2 (i : Fin 3) : B4 (aC4' (2, i)) = vface (k := 1) i (fun k => colTri4 2 k + colLam4 2) := by
  rw [cS4_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_3 (i : Fin 3) : B4 (aC4' (3, i)) = vface (k := 1) i (fun k => colTri4 3 k + colLam4 3) := by
  rw [cS4_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_4 (i : Fin 3) : B4 (aC4' (4, i)) = vface (k := 1) i (fun k => colTri4 4 k + colLam4 4) := by
  rw [cS4_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_5 (i : Fin 3) : B4 (aC4' (5, i)) = vface (k := 1) i (fun k => colTri4 5 k + colLam4 5) := by
  rw [cS4_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_6 (i : Fin 3) : B4 (aC4' (6, i)) = vface (k := 1) i (fun k => colTri4 6 k + colLam4 6) := by
  rw [cS4_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_7 (i : Fin 3) : B4 (aC4' (7, i)) = vface (k := 1) i (fun k => colTri4 7 k + colLam4 7) := by
  rw [cS4_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_8 (i : Fin 3) : B4 (aC4' (8, i)) = vface (k := 1) i (fun k => colTri4 8 k + colLam4 8) := by
  rw [cS4_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_9 (i : Fin 3) : B4 (aC4' (9, i)) = vface (k := 1) i (fun k => colTri4 9 k + colLam4 9) := by
  rw [cS4_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_10 (i : Fin 3) : B4 (aC4' (10, i)) = vface (k := 1) i (fun k => colTri4 10 k + colLam4 10) := by
  rw [cS4_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_11 (i : Fin 3) : B4 (aC4' (11, i)) = vface (k := 1) i (fun k => colTri4 11 k + colLam4 11) := by
  rw [cS4_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_12 (i : Fin 3) : B4 (aC4' (12, i)) = vface (k := 1) i (fun k => colTri4 12 k + colLam4 12) := by
  rw [cS4_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_13 (i : Fin 3) : B4 (aC4' (13, i)) = vface (k := 1) i (fun k => colTri4 13 k + colLam4 13) := by
  rw [cS4_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_14 (i : Fin 3) : B4 (aC4' (14, i)) = vface (k := 1) i (fun k => colTri4 14 k + colLam4 14) := by
  rw [cS4_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_15 (i : Fin 3) : B4 (aC4' (15, i)) = vface (k := 1) i (fun k => colTri4 15 k + colLam4 15) := by
  rw [cS4_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_16 (i : Fin 3) : B4 (aC4' (16, i)) = vface (k := 1) i (fun k => colTri4 16 k + colLam4 16) := by
  rw [cS4_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_17 (i : Fin 3) : B4 (aC4' (17, i)) = vface (k := 1) i (fun k => colTri4 17 k + colLam4 17) := by
  rw [cS4_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_18 (i : Fin 3) : B4 (aC4' (18, i)) = vface (k := 1) i (fun k => colTri4 18 k + colLam4 18) := by
  rw [cS4_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_19 (i : Fin 3) : B4 (aC4' (19, i)) = vface (k := 1) i (fun k => colTri4 19 k + colLam4 19) := by
  rw [cS4_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_20 (i : Fin 3) : B4 (aC4' (20, i)) = vface (k := 1) i (fun k => colTri4 20 k + colLam4 20) := by
  rw [cS4_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_21 (i : Fin 3) : B4 (aC4' (21, i)) = vface (k := 1) i (fun k => colTri4 21 k + colLam4 21) := by
  rw [cS4_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_22 (i : Fin 3) : B4 (aC4' (22, i)) = vface (k := 1) i (fun k => colTri4 22 k + colLam4 22) := by
  rw [cS4_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_23 (i : Fin 3) : B4 (aC4' (23, i)) = vface (k := 1) i (fun k => colTri4 23 k + colLam4 23) := by
  rw [cS4_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_24 (i : Fin 3) : B4 (aC4' (24, i)) = vface (k := 1) i (fun k => colTri4 24 k + colLam4 24) := by
  rw [cS4_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_25 (i : Fin 3) : B4 (aC4' (25, i)) = vface (k := 1) i (fun k => colTri4 25 k + colLam4 25) := by
  rw [cS4_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_26 (i : Fin 3) : B4 (aC4' (26, i)) = vface (k := 1) i (fun k => colTri4 26 k + colLam4 26) := by
  rw [cS4_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_27 (i : Fin 3) : B4 (aC4' (27, i)) = vface (k := 1) i (fun k => colTri4 27 k + colLam4 27) := by
  rw [cS4_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_28 (i : Fin 3) : B4 (aC4' (28, i)) = vface (k := 1) i (fun k => colTri4 28 k + colLam4 28) := by
  rw [cS4_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_29 (i : Fin 3) : B4 (aC4' (29, i)) = vface (k := 1) i (fun k => colTri4 29 k + colLam4 29) := by
  rw [cS4_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_30 (i : Fin 3) : B4 (aC4' (30, i)) = vface (k := 1) i (fun k => colTri4 30 k + colLam4 30) := by
  rw [cS4_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_31 (i : Fin 3) : B4 (aC4' (31, i)) = vface (k := 1) i (fun k => colTri4 31 k + colLam4 31) := by
  rw [cS4_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_32 (i : Fin 3) : B4 (aC4' (32, i)) = vface (k := 1) i (fun k => colTri4 32 k + colLam4 32) := by
  rw [cS4_32]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_33 (i : Fin 3) : B4 (aC4' (33, i)) = vface (k := 1) i (fun k => colTri4 33 k + colLam4 33) := by
  rw [cS4_33]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_34 (i : Fin 3) : B4 (aC4' (34, i)) = vface (k := 1) i (fun k => colTri4 34 k + colLam4 34) := by
  rw [cS4_34]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_35 (i : Fin 3) : B4 (aC4' (35, i)) = vface (k := 1) i (fun k => colTri4 35 k + colLam4 35) := by
  rw [cS4_35]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_36 (i : Fin 3) : B4 (aC4' (36, i)) = vface (k := 1) i (fun k => colTri4 36 k + colLam4 36) := by
  rw [cS4_36]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_37 (i : Fin 3) : B4 (aC4' (37, i)) = vface (k := 1) i (fun k => colTri4 37 k + colLam4 37) := by
  rw [cS4_37]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_38 (i : Fin 3) : B4 (aC4' (38, i)) = vface (k := 1) i (fun k => colTri4 38 k + colLam4 38) := by
  rw [cS4_38]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_39 (i : Fin 3) : B4 (aC4' (39, i)) = vface (k := 1) i (fun k => colTri4 39 k + colLam4 39) := by
  rw [cS4_39]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_40 (i : Fin 3) : B4 (aC4' (40, i)) = vface (k := 1) i (fun k => colTri4 40 k + colLam4 40) := by
  rw [cS4_40]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_41 (i : Fin 3) : B4 (aC4' (41, i)) = vface (k := 1) i (fun k => colTri4 41 k + colLam4 41) := by
  rw [cS4_41]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_42 (i : Fin 3) : B4 (aC4' (42, i)) = vface (k := 1) i (fun k => colTri4 42 k + colLam4 42) := by
  rw [cS4_42]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_43 (i : Fin 3) : B4 (aC4' (43, i)) = vface (k := 1) i (fun k => colTri4 43 k + colLam4 43) := by
  rw [cS4_43]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_44 (i : Fin 3) : B4 (aC4' (44, i)) = vface (k := 1) i (fun k => colTri4 44 k + colLam4 44) := by
  rw [cS4_44]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_45 (i : Fin 3) : B4 (aC4' (45, i)) = vface (k := 1) i (fun k => colTri4 45 k + colLam4 45) := by
  rw [cS4_45]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_46 (i : Fin 3) : B4 (aC4' (46, i)) = vface (k := 1) i (fun k => colTri4 46 k + colLam4 46) := by
  rw [cS4_46]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brC4'_47 (i : Fin 3) : B4 (aC4' (47, i)) = vface (k := 1) i (fun k => colTri4 47 k + colLam4 47) := by
  rw [cS4_47]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_0 (i : Fin 3) : B4 (aW4 (0, i)) = vface (k := 1) i (fun k => tauV4 0 k + lamV4 0) := by
  rw [tS4_0]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_1 (i : Fin 3) : B4 (aW4 (1, i)) = vface (k := 1) i (fun k => tauV4 1 k + lamV4 1) := by
  rw [tS4_1]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_2 (i : Fin 3) : B4 (aW4 (2, i)) = vface (k := 1) i (fun k => tauV4 2 k + lamV4 2) := by
  rw [tS4_2]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_3 (i : Fin 3) : B4 (aW4 (3, i)) = vface (k := 1) i (fun k => tauV4 3 k + lamV4 3) := by
  rw [tS4_3]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_4 (i : Fin 3) : B4 (aW4 (4, i)) = vface (k := 1) i (fun k => tauV4 4 k + lamV4 4) := by
  rw [tS4_4]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_5 (i : Fin 3) : B4 (aW4 (5, i)) = vface (k := 1) i (fun k => tauV4 5 k + lamV4 5) := by
  rw [tS4_5]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_6 (i : Fin 3) : B4 (aW4 (6, i)) = vface (k := 1) i (fun k => tauV4 6 k + lamV4 6) := by
  rw [tS4_6]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_7 (i : Fin 3) : B4 (aW4 (7, i)) = vface (k := 1) i (fun k => tauV4 7 k + lamV4 7) := by
  rw [tS4_7]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_8 (i : Fin 3) : B4 (aW4 (8, i)) = vface (k := 1) i (fun k => tauV4 8 k + lamV4 8) := by
  rw [tS4_8]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_9 (i : Fin 3) : B4 (aW4 (9, i)) = vface (k := 1) i (fun k => tauV4 9 k + lamV4 9) := by
  rw [tS4_9]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_10 (i : Fin 3) : B4 (aW4 (10, i)) = vface (k := 1) i (fun k => tauV4 10 k + lamV4 10) := by
  rw [tS4_10]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_11 (i : Fin 3) : B4 (aW4 (11, i)) = vface (k := 1) i (fun k => tauV4 11 k + lamV4 11) := by
  rw [tS4_11]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_12 (i : Fin 3) : B4 (aW4 (12, i)) = vface (k := 1) i (fun k => tauV4 12 k + lamV4 12) := by
  rw [tS4_12]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_13 (i : Fin 3) : B4 (aW4 (13, i)) = vface (k := 1) i (fun k => tauV4 13 k + lamV4 13) := by
  rw [tS4_13]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_14 (i : Fin 3) : B4 (aW4 (14, i)) = vface (k := 1) i (fun k => tauV4 14 k + lamV4 14) := by
  rw [tS4_14]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_15 (i : Fin 3) : B4 (aW4 (15, i)) = vface (k := 1) i (fun k => tauV4 15 k + lamV4 15) := by
  rw [tS4_15]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_16 (i : Fin 3) : B4 (aW4 (16, i)) = vface (k := 1) i (fun k => tauV4 16 k + lamV4 16) := by
  rw [tS4_16]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_17 (i : Fin 3) : B4 (aW4 (17, i)) = vface (k := 1) i (fun k => tauV4 17 k + lamV4 17) := by
  rw [tS4_17]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_18 (i : Fin 3) : B4 (aW4 (18, i)) = vface (k := 1) i (fun k => tauV4 18 k + lamV4 18) := by
  rw [tS4_18]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_19 (i : Fin 3) : B4 (aW4 (19, i)) = vface (k := 1) i (fun k => tauV4 19 k + lamV4 19) := by
  rw [tS4_19]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_20 (i : Fin 3) : B4 (aW4 (20, i)) = vface (k := 1) i (fun k => tauV4 20 k + lamV4 20) := by
  rw [tS4_20]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_21 (i : Fin 3) : B4 (aW4 (21, i)) = vface (k := 1) i (fun k => tauV4 21 k + lamV4 21) := by
  rw [tS4_21]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_22 (i : Fin 3) : B4 (aW4 (22, i)) = vface (k := 1) i (fun k => tauV4 22 k + lamV4 22) := by
  rw [tS4_22]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_23 (i : Fin 3) : B4 (aW4 (23, i)) = vface (k := 1) i (fun k => tauV4 23 k + lamV4 23) := by
  rw [tS4_23]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_24 (i : Fin 3) : B4 (aW4 (24, i)) = vface (k := 1) i (fun k => tauV4 24 k + lamV4 24) := by
  rw [tS4_24]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_25 (i : Fin 3) : B4 (aW4 (25, i)) = vface (k := 1) i (fun k => tauV4 25 k + lamV4 25) := by
  rw [tS4_25]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_26 (i : Fin 3) : B4 (aW4 (26, i)) = vface (k := 1) i (fun k => tauV4 26 k + lamV4 26) := by
  rw [tS4_26]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_27 (i : Fin 3) : B4 (aW4 (27, i)) = vface (k := 1) i (fun k => tauV4 27 k + lamV4 27) := by
  rw [tS4_27]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_28 (i : Fin 3) : B4 (aW4 (28, i)) = vface (k := 1) i (fun k => tauV4 28 k + lamV4 28) := by
  rw [tS4_28]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_29 (i : Fin 3) : B4 (aW4 (29, i)) = vface (k := 1) i (fun k => tauV4 29 k + lamV4 29) := by
  rw [tS4_29]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_30 (i : Fin 3) : B4 (aW4 (30, i)) = vface (k := 1) i (fun k => tauV4 30 k + lamV4 30) := by
  rw [tS4_30]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_31 (i : Fin 3) : B4 (aW4 (31, i)) = vface (k := 1) i (fun k => tauV4 31 k + lamV4 31) := by
  rw [tS4_31]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_32 (i : Fin 3) : B4 (aW4 (32, i)) = vface (k := 1) i (fun k => tauV4 32 k + lamV4 32) := by
  rw [tS4_32]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_33 (i : Fin 3) : B4 (aW4 (33, i)) = vface (k := 1) i (fun k => tauV4 33 k + lamV4 33) := by
  rw [tS4_33]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_34 (i : Fin 3) : B4 (aW4 (34, i)) = vface (k := 1) i (fun k => tauV4 34 k + lamV4 34) := by
  rw [tS4_34]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_35 (i : Fin 3) : B4 (aW4 (35, i)) = vface (k := 1) i (fun k => tauV4 35 k + lamV4 35) := by
  rw [tS4_35]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_36 (i : Fin 3) : B4 (aW4 (36, i)) = vface (k := 1) i (fun k => tauV4 36 k + lamV4 36) := by
  rw [tS4_36]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_37 (i : Fin 3) : B4 (aW4 (37, i)) = vface (k := 1) i (fun k => tauV4 37 k + lamV4 37) := by
  rw [tS4_37]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_38 (i : Fin 3) : B4 (aW4 (38, i)) = vface (k := 1) i (fun k => tauV4 38 k + lamV4 38) := by
  rw [tS4_38]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_39 (i : Fin 3) : B4 (aW4 (39, i)) = vface (k := 1) i (fun k => tauV4 39 k + lamV4 39) := by
  rw [tS4_39]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_40 (i : Fin 3) : B4 (aW4 (40, i)) = vface (k := 1) i (fun k => tauV4 40 k + lamV4 40) := by
  rw [tS4_40]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_41 (i : Fin 3) : B4 (aW4 (41, i)) = vface (k := 1) i (fun k => tauV4 41 k + lamV4 41) := by
  rw [tS4_41]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_42 (i : Fin 3) : B4 (aW4 (42, i)) = vface (k := 1) i (fun k => tauV4 42 k + lamV4 42) := by
  rw [tS4_42]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_43 (i : Fin 3) : B4 (aW4 (43, i)) = vface (k := 1) i (fun k => tauV4 43 k + lamV4 43) := by
  rw [tS4_43]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_44 (i : Fin 3) : B4 (aW4 (44, i)) = vface (k := 1) i (fun k => tauV4 44 k + lamV4 44) := by
  rw [tS4_44]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_45 (i : Fin 3) : B4 (aW4 (45, i)) = vface (k := 1) i (fun k => tauV4 45 k + lamV4 45) := by
  rw [tS4_45]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_46 (i : Fin 3) : B4 (aW4 (46, i)) = vface (k := 1) i (fun k => tauV4 46 k + lamV4 46) := by
  rw [tS4_46]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_47 (i : Fin 3) : B4 (aW4 (47, i)) = vface (k := 1) i (fun k => tauV4 47 k + lamV4 47) := by
  rw [tS4_47]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_48 (i : Fin 3) : B4 (aW4 (48, i)) = vface (k := 1) i (fun k => tauV4 48 k + lamV4 48) := by
  rw [tS4_48]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_49 (i : Fin 3) : B4 (aW4 (49, i)) = vface (k := 1) i (fun k => tauV4 49 k + lamV4 49) := by
  rw [tS4_49]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_50 (i : Fin 3) : B4 (aW4 (50, i)) = vface (k := 1) i (fun k => tauV4 50 k + lamV4 50) := by
  rw [tS4_50]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_51 (i : Fin 3) : B4 (aW4 (51, i)) = vface (k := 1) i (fun k => tauV4 51 k + lamV4 51) := by
  rw [tS4_51]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_52 (i : Fin 3) : B4 (aW4 (52, i)) = vface (k := 1) i (fun k => tauV4 52 k + lamV4 52) := by
  rw [tS4_52]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_53 (i : Fin 3) : B4 (aW4 (53, i)) = vface (k := 1) i (fun k => tauV4 53 k + lamV4 53) := by
  rw [tS4_53]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_54 (i : Fin 3) : B4 (aW4 (54, i)) = vface (k := 1) i (fun k => tauV4 54 k + lamV4 54) := by
  rw [tS4_54]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_55 (i : Fin 3) : B4 (aW4 (55, i)) = vface (k := 1) i (fun k => tauV4 55 k + lamV4 55) := by
  rw [tS4_55]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_56 (i : Fin 3) : B4 (aW4 (56, i)) = vface (k := 1) i (fun k => tauV4 56 k + lamV4 56) := by
  rw [tS4_56]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_57 (i : Fin 3) : B4 (aW4 (57, i)) = vface (k := 1) i (fun k => tauV4 57 k + lamV4 57) := by
  rw [tS4_57]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_58 (i : Fin 3) : B4 (aW4 (58, i)) = vface (k := 1) i (fun k => tauV4 58 k + lamV4 58) := by
  rw [tS4_58]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_59 (i : Fin 3) : B4 (aW4 (59, i)) = vface (k := 1) i (fun k => tauV4 59 k + lamV4 59) := by
  rw [tS4_59]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_60 (i : Fin 3) : B4 (aW4 (60, i)) = vface (k := 1) i (fun k => tauV4 60 k + lamV4 60) := by
  rw [tS4_60]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_61 (i : Fin 3) : B4 (aW4 (61, i)) = vface (k := 1) i (fun k => tauV4 61 k + lamV4 61) := by
  rw [tS4_61]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_62 (i : Fin 3) : B4 (aW4 (62, i)) = vface (k := 1) i (fun k => tauV4 62 k + lamV4 62) := by
  rw [tS4_62]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_63 (i : Fin 3) : B4 (aW4 (63, i)) = vface (k := 1) i (fun k => tauV4 63 k + lamV4 63) := by
  rw [tS4_63]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_64 (i : Fin 3) : B4 (aW4 (64, i)) = vface (k := 1) i (fun k => tauV4 64 k + lamV4 64) := by
  rw [tS4_64]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_65 (i : Fin 3) : B4 (aW4 (65, i)) = vface (k := 1) i (fun k => tauV4 65 k + lamV4 65) := by
  rw [tS4_65]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_66 (i : Fin 3) : B4 (aW4 (66, i)) = vface (k := 1) i (fun k => tauV4 66 k + lamV4 66) := by
  rw [tS4_66]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_67 (i : Fin 3) : B4 (aW4 (67, i)) = vface (k := 1) i (fun k => tauV4 67 k + lamV4 67) := by
  rw [tS4_67]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_68 (i : Fin 3) : B4 (aW4 (68, i)) = vface (k := 1) i (fun k => tauV4 68 k + lamV4 68) := by
  rw [tS4_68]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_69 (i : Fin 3) : B4 (aW4 (69, i)) = vface (k := 1) i (fun k => tauV4 69 k + lamV4 69) := by
  rw [tS4_69]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_70 (i : Fin 3) : B4 (aW4 (70, i)) = vface (k := 1) i (fun k => tauV4 70 k + lamV4 70) := by
  rw [tS4_70]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_71 (i : Fin 3) : B4 (aW4 (71, i)) = vface (k := 1) i (fun k => tauV4 71 k + lamV4 71) := by
  rw [tS4_71]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_72 (i : Fin 3) : B4 (aW4 (72, i)) = vface (k := 1) i (fun k => tauV4 72 k + lamV4 72) := by
  rw [tS4_72]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_73 (i : Fin 3) : B4 (aW4 (73, i)) = vface (k := 1) i (fun k => tauV4 73 k + lamV4 73) := by
  rw [tS4_73]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_74 (i : Fin 3) : B4 (aW4 (74, i)) = vface (k := 1) i (fun k => tauV4 74 k + lamV4 74) := by
  rw [tS4_74]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_75 (i : Fin 3) : B4 (aW4 (75, i)) = vface (k := 1) i (fun k => tauV4 75 k + lamV4 75) := by
  rw [tS4_75]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_76 (i : Fin 3) : B4 (aW4 (76, i)) = vface (k := 1) i (fun k => tauV4 76 k + lamV4 76) := by
  rw [tS4_76]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_77 (i : Fin 3) : B4 (aW4 (77, i)) = vface (k := 1) i (fun k => tauV4 77 k + lamV4 77) := by
  rw [tS4_77]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_78 (i : Fin 3) : B4 (aW4 (78, i)) = vface (k := 1) i (fun k => tauV4 78 k + lamV4 78) := by
  rw [tS4_78]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_79 (i : Fin 3) : B4 (aW4 (79, i)) = vface (k := 1) i (fun k => tauV4 79 k + lamV4 79) := by
  rw [tS4_79]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_80 (i : Fin 3) : B4 (aW4 (80, i)) = vface (k := 1) i (fun k => tauV4 80 k + lamV4 80) := by
  rw [tS4_80]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_81 (i : Fin 3) : B4 (aW4 (81, i)) = vface (k := 1) i (fun k => tauV4 81 k + lamV4 81) := by
  rw [tS4_81]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_82 (i : Fin 3) : B4 (aW4 (82, i)) = vface (k := 1) i (fun k => tauV4 82 k + lamV4 82) := by
  rw [tS4_82]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_83 (i : Fin 3) : B4 (aW4 (83, i)) = vface (k := 1) i (fun k => tauV4 83 k + lamV4 83) := by
  rw [tS4_83]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_84 (i : Fin 3) : B4 (aW4 (84, i)) = vface (k := 1) i (fun k => tauV4 84 k + lamV4 84) := by
  rw [tS4_84]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_85 (i : Fin 3) : B4 (aW4 (85, i)) = vface (k := 1) i (fun k => tauV4 85 k + lamV4 85) := by
  rw [tS4_85]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_86 (i : Fin 3) : B4 (aW4 (86, i)) = vface (k := 1) i (fun k => tauV4 86 k + lamV4 86) := by
  rw [tS4_86]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_87 (i : Fin 3) : B4 (aW4 (87, i)) = vface (k := 1) i (fun k => tauV4 87 k + lamV4 87) := by
  rw [tS4_87]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_88 (i : Fin 3) : B4 (aW4 (88, i)) = vface (k := 1) i (fun k => tauV4 88 k + lamV4 88) := by
  rw [tS4_88]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_89 (i : Fin 3) : B4 (aW4 (89, i)) = vface (k := 1) i (fun k => tauV4 89 k + lamV4 89) := by
  rw [tS4_89]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_90 (i : Fin 3) : B4 (aW4 (90, i)) = vface (k := 1) i (fun k => tauV4 90 k + lamV4 90) := by
  rw [tS4_90]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_91 (i : Fin 3) : B4 (aW4 (91, i)) = vface (k := 1) i (fun k => tauV4 91 k + lamV4 91) := by
  rw [tS4_91]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_92 (i : Fin 3) : B4 (aW4 (92, i)) = vface (k := 1) i (fun k => tauV4 92 k + lamV4 92) := by
  rw [tS4_92]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_93 (i : Fin 3) : B4 (aW4 (93, i)) = vface (k := 1) i (fun k => tauV4 93 k + lamV4 93) := by
  rw [tS4_93]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_94 (i : Fin 3) : B4 (aW4 (94, i)) = vface (k := 1) i (fun k => tauV4 94 k + lamV4 94) := by
  rw [tS4_94]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_95 (i : Fin 3) : B4 (aW4 (95, i)) = vface (k := 1) i (fun k => tauV4 95 k + lamV4 95) := by
  rw [tS4_95]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_96 (i : Fin 3) : B4 (aW4 (96, i)) = vface (k := 1) i (fun k => tauV4 96 k + lamV4 96) := by
  rw [tS4_96]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_97 (i : Fin 3) : B4 (aW4 (97, i)) = vface (k := 1) i (fun k => tauV4 97 k + lamV4 97) := by
  rw [tS4_97]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_98 (i : Fin 3) : B4 (aW4 (98, i)) = vface (k := 1) i (fun k => tauV4 98 k + lamV4 98) := by
  rw [tS4_98]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_99 (i : Fin 3) : B4 (aW4 (99, i)) = vface (k := 1) i (fun k => tauV4 99 k + lamV4 99) := by
  rw [tS4_99]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_100 (i : Fin 3) : B4 (aW4 (100, i)) = vface (k := 1) i (fun k => tauV4 100 k + lamV4 100) := by
  rw [tS4_100]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_101 (i : Fin 3) : B4 (aW4 (101, i)) = vface (k := 1) i (fun k => tauV4 101 k + lamV4 101) := by
  rw [tS4_101]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_102 (i : Fin 3) : B4 (aW4 (102, i)) = vface (k := 1) i (fun k => tauV4 102 k + lamV4 102) := by
  rw [tS4_102]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_103 (i : Fin 3) : B4 (aW4 (103, i)) = vface (k := 1) i (fun k => tauV4 103 k + lamV4 103) := by
  rw [tS4_103]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_104 (i : Fin 3) : B4 (aW4 (104, i)) = vface (k := 1) i (fun k => tauV4 104 k + lamV4 104) := by
  rw [tS4_104]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_105 (i : Fin 3) : B4 (aW4 (105, i)) = vface (k := 1) i (fun k => tauV4 105 k + lamV4 105) := by
  rw [tS4_105]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_106 (i : Fin 3) : B4 (aW4 (106, i)) = vface (k := 1) i (fun k => tauV4 106 k + lamV4 106) := by
  rw [tS4_106]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_107 (i : Fin 3) : B4 (aW4 (107, i)) = vface (k := 1) i (fun k => tauV4 107 k + lamV4 107) := by
  rw [tS4_107]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_108 (i : Fin 3) : B4 (aW4 (108, i)) = vface (k := 1) i (fun k => tauV4 108 k + lamV4 108) := by
  rw [tS4_108]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_109 (i : Fin 3) : B4 (aW4 (109, i)) = vface (k := 1) i (fun k => tauV4 109 k + lamV4 109) := by
  rw [tS4_109]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_110 (i : Fin 3) : B4 (aW4 (110, i)) = vface (k := 1) i (fun k => tauV4 110 k + lamV4 110) := by
  rw [tS4_110]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_111 (i : Fin 3) : B4 (aW4 (111, i)) = vface (k := 1) i (fun k => tauV4 111 k + lamV4 111) := by
  rw [tS4_111]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_112 (i : Fin 3) : B4 (aW4 (112, i)) = vface (k := 1) i (fun k => tauV4 112 k + lamV4 112) := by
  rw [tS4_112]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_113 (i : Fin 3) : B4 (aW4 (113, i)) = vface (k := 1) i (fun k => tauV4 113 k + lamV4 113) := by
  rw [tS4_113]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_114 (i : Fin 3) : B4 (aW4 (114, i)) = vface (k := 1) i (fun k => tauV4 114 k + lamV4 114) := by
  rw [tS4_114]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_115 (i : Fin 3) : B4 (aW4 (115, i)) = vface (k := 1) i (fun k => tauV4 115 k + lamV4 115) := by
  rw [tS4_115]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_116 (i : Fin 3) : B4 (aW4 (116, i)) = vface (k := 1) i (fun k => tauV4 116 k + lamV4 116) := by
  rw [tS4_116]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_117 (i : Fin 3) : B4 (aW4 (117, i)) = vface (k := 1) i (fun k => tauV4 117 k + lamV4 117) := by
  rw [tS4_117]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_118 (i : Fin 3) : B4 (aW4 (118, i)) = vface (k := 1) i (fun k => tauV4 118 k + lamV4 118) := by
  rw [tS4_118]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_119 (i : Fin 3) : B4 (aW4 (119, i)) = vface (k := 1) i (fun k => tauV4 119 k + lamV4 119) := by
  rw [tS4_119]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_120 (i : Fin 3) : B4 (aW4 (120, i)) = vface (k := 1) i (fun k => tauV4 120 k + lamV4 120) := by
  rw [tS4_120]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_121 (i : Fin 3) : B4 (aW4 (121, i)) = vface (k := 1) i (fun k => tauV4 121 k + lamV4 121) := by
  rw [tS4_121]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_122 (i : Fin 3) : B4 (aW4 (122, i)) = vface (k := 1) i (fun k => tauV4 122 k + lamV4 122) := by
  rw [tS4_122]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_123 (i : Fin 3) : B4 (aW4 (123, i)) = vface (k := 1) i (fun k => tauV4 123 k + lamV4 123) := by
  rw [tS4_123]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_124 (i : Fin 3) : B4 (aW4 (124, i)) = vface (k := 1) i (fun k => tauV4 124 k + lamV4 124) := by
  rw [tS4_124]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_125 (i : Fin 3) : B4 (aW4 (125, i)) = vface (k := 1) i (fun k => tauV4 125 k + lamV4 125) := by
  rw [tS4_125]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_126 (i : Fin 3) : B4 (aW4 (126, i)) = vface (k := 1) i (fun k => tauV4 126 k + lamV4 126) := by
  rw [tS4_126]; fin_cases i <;> funext k <;> fin_cases k <;> rfl
theorem brW4_127 (i : Fin 3) : B4 (aW4 (127, i)) = vface (k := 1) i (fun k => tauV4 127 k + lamV4 127) := by
  rw [tS4_127]; fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- The atoms of the second edge family of the collar. -/
theorem brC4' : ∀ p : Fin 48 × Fin 3,
    B4 (aC4' p) = vface (k := 1) p.2 (fun k => colTri4 p.1 k + colLam4 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brC4'_0 i, brC4'_1 i, brC4'_2 i, brC4'_3 i, brC4'_4 i, brC4'_5 i, brC4'_6 i, brC4'_7 i, brC4'_8 i, brC4'_9 i, brC4'_10 i, brC4'_11 i, brC4'_12 i, brC4'_13 i, brC4'_14 i, brC4'_15 i, brC4'_16 i, brC4'_17 i, brC4'_18 i, brC4'_19 i, brC4'_20 i, brC4'_21 i, brC4'_22 i, brC4'_23 i, brC4'_24 i, brC4'_25 i, brC4'_26 i, brC4'_27 i, brC4'_28 i, brC4'_29 i, brC4'_30 i, brC4'_31 i, brC4'_32 i, brC4'_33 i, brC4'_34 i, brC4'_35 i, brC4'_36 i, brC4'_37 i, brC4'_38 i, brC4'_39 i, brC4'_40 i, brC4'_41 i, brC4'_42 i, brC4'_43 i, brC4'_44 i, brC4'_45 i, brC4'_46 i, brC4'_47 i]

/-- The atoms of the edges of the wall. -/
theorem brW4 : ∀ p : Fin 128 × Fin 3,
    B4 (aW4 p) = vface (k := 1) p.2 (fun k => tauV4 p.1 k + lamV4 p.1) := by
  rintro ⟨j, i⟩
  fin_cases j
  exacts [brW4_0 i, brW4_1 i, brW4_2 i, brW4_3 i, brW4_4 i, brW4_5 i, brW4_6 i, brW4_7 i, brW4_8 i, brW4_9 i, brW4_10 i, brW4_11 i, brW4_12 i, brW4_13 i, brW4_14 i, brW4_15 i, brW4_16 i, brW4_17 i, brW4_18 i, brW4_19 i, brW4_20 i, brW4_21 i, brW4_22 i, brW4_23 i, brW4_24 i, brW4_25 i, brW4_26 i, brW4_27 i, brW4_28 i, brW4_29 i, brW4_30 i, brW4_31 i, brW4_32 i, brW4_33 i, brW4_34 i, brW4_35 i, brW4_36 i, brW4_37 i, brW4_38 i, brW4_39 i, brW4_40 i, brW4_41 i, brW4_42 i, brW4_43 i, brW4_44 i, brW4_45 i, brW4_46 i, brW4_47 i, brW4_48 i, brW4_49 i, brW4_50 i, brW4_51 i, brW4_52 i, brW4_53 i, brW4_54 i, brW4_55 i, brW4_56 i, brW4_57 i, brW4_58 i, brW4_59 i, brW4_60 i, brW4_61 i, brW4_62 i, brW4_63 i, brW4_64 i, brW4_65 i, brW4_66 i, brW4_67 i, brW4_68 i, brW4_69 i, brW4_70 i, brW4_71 i, brW4_72 i, brW4_73 i, brW4_74 i, brW4_75 i, brW4_76 i, brW4_77 i, brW4_78 i, brW4_79 i, brW4_80 i, brW4_81 i, brW4_82 i, brW4_83 i, brW4_84 i, brW4_85 i, brW4_86 i, brW4_87 i, brW4_88 i, brW4_89 i, brW4_90 i, brW4_91 i, brW4_92 i, brW4_93 i, brW4_94 i, brW4_95 i, brW4_96 i, brW4_97 i, brW4_98 i, brW4_99 i, brW4_100 i, brW4_101 i, brW4_102 i, brW4_103 i, brW4_104 i, brW4_105 i, brW4_106 i, brW4_107 i, brW4_108 i, brW4_109 i, brW4_110 i, brW4_111 i, brW4_112 i, brW4_113 i, brW4_114 i, brW4_115 i, brW4_116 i, brW4_117 i, brW4_118 i, brW4_119 i, brW4_120 i, brW4_121 i, brW4_122 i, brW4_123 i, brW4_124 i, brW4_125 i, brW4_126 i, brW4_127 i]

/-- The atoms of the first coarse triangle. -/
theorem brB40 : ∀ i : Fin 3, B4 (aB40 i) = vface (k := 1) i botV0 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

/-- The atoms of the second coarse triangle. -/
theorem brB41 : ∀ i : Fin 3, B4 (aB41 i) = vface (k := 1) i botV1 := by
  intro i
  fin_cases i <;>
    · funext k
      fin_cases k <;> rfl

theorem colLam_mem4 (j : NCol4) : slabL 4 (colLam4 j) ∈ Work.Cusp.lattice 4 := by
  have h : slabL 4 (colLam4 j) ∈ ({Work.Cusp.kv 4 1, Work.Cusp.kv 4 2} : Set CuspE3) := by
    fin_cases j <;> simp [colLam4, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3]
  rcases h with h | h
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 1)
  · rw [h]; exact AddSubgroup.subset_closure (Set.mem_range_self 2)

/-- **The collar of cusp `4` is in the kernel of `slabChain`.** -/
theorem collar_slab4 : slabChain 4 2 (collarChain4 : AffC 2) = 0 := by
  rw [collarChain4, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, map_sub, slabChain_single_one, slabChain_single_one]
  have h1 : slabV 4 (fun k => colTri4 j k + colLam4 j)
      = fun k => slabV 4 (colTri4 j) k + slabL 4 (colLam4 j) := by
    funext k; simp only [slabV, slabL_add]
  rw [h1, cChain_add_lattice 4 (slabV 4 (colTri4 j)) (slabL 4 (colLam4 j))
        (colLam_mem4 j), sub_self, smul_zero]

/-- **The boundary of the collar of cusp `4`.** -/
theorem dLC_collar4 :
    dLC 1 (collarChain4 : AffC 2) = dLC 1 (wallChain4 : AffC 2) - dLC 1 slabBot := by
  have hP1 : (∑ j : NCol4, dLC 1 (colCoef4 j • Finsupp.single (colTri4 j) (1 : ℤ)))
      = ∑ p : Fin 48 × Fin 3, cC4 p • X4 (aC4 p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC4, ← smul_smul, ← brC4 (j, i)]
  have hP2 : (∑ j : NCol4, dLC 1 (colCoef4 j •
        Finsupp.single (fun k => colTri4 j k + colLam4 j) (1 : ℤ)))
      = ∑ p : Fin 48 × Fin 3, cC4' p • X4 (aC4' p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cC4', ← smul_smul, ← brC4' (j, i)]
  have hQ1 : (∑ p : Fin 48 × Fin 3, cC4 p • X4 (aC4 p))
      = ∑ l : Fin Nat4, D14 l • X4 l :=
    sum_smul_regroup aC4 cC4 X4
  have hQ2 : (∑ p : Fin 48 × Fin 3, cC4' p • X4 (aC4' p))
      = ∑ l : Fin Nat4, D24 l • X4 l :=
    sum_smul_regroup aC4' cC4' X4
  have hW : (∑ p : Fin 128 × Fin 3, cW4 p • X4 (aW4 p))
      = ∑ l : Fin Nat4, D34 l • X4 l :=
    sum_smul_regroup aW4 cW4 X4
  have hB0 : (∑ i : Fin 3, cB4 i • X4 (aB40 i))
      = ∑ l : Fin Nat4, D44 l • X4 l :=
    sum_smul_regroup aB40 cB4 X4
  have hB1 : (∑ i : Fin 3, cB4 i • X4 (aB41 i))
      = ∑ l : Fin Nat4, D54 l • X4 l :=
    sum_smul_regroup aB41 cB4 X4
  have hwall : dLC 1 (wallChain4 : AffC 2)
      = ∑ p : Fin 128 × Fin 3, cW4 p • X4 (aW4 p) := by
    rw [wallChain4, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, dLC_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cW4, ← smul_smul, ← brW4 (j, i)]
  have hbot : dLC 1 slabBot
      = (∑ i : Fin 3, cB4 i • X4 (aB40 i))
        - (∑ i : Fin 3, cB4 i • X4 (aB41 i)) := by
    rw [slabBot, map_sub, dLC_single, dLC_single]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB4, ← brB40 i]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [cB4, ← brB41 i]
  have hcol : dLC 1 (collarChain4 : AffC 2)
      = (∑ j : NCol4, dLC 1 (colCoef4 j • Finsupp.single (colTri4 j) (1 : ℤ)))
        - (∑ j : NCol4, dLC 1 (colCoef4 j •
            Finsupp.single (fun k => colTri4 j k + colLam4 j) (1 : ℤ))) := by
    rw [collarChain4, map_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, smul_sub, map_smul, map_smul]
  have hcoef : ∀ l : Fin Nat4, D14 l - D24 l = D34 l - (D44 l - D54 l) := hcoef4
  rw [hcol, hP1, hP2, hQ1, hQ2, hwall, hW, hbot, hB0, hB1]
  exact sum_smul_four D14 D24 D34 D44 D54 X4 hcoef

end

end Work.BridgeSquare.SlabBuild

