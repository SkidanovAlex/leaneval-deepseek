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
theorem hcoef4_c0 : ∀ l : Fin Nat4, 0 ≤ l.val → l.val < 40 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c1 : ∀ l : Fin Nat4, 40 ≤ l.val → l.val < 80 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c2 : ∀ l : Fin Nat4, 80 ≤ l.val → l.val < 120 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c3 : ∀ l : Fin Nat4, 120 ≤ l.val → l.val < 160 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c4 : ∀ l : Fin Nat4, 160 ≤ l.val → l.val < 200 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c5 : ∀ l : Fin Nat4, 200 ≤ l.val → l.val < 240 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c6 : ∀ l : Fin Nat4, 240 ≤ l.val → l.val < 280 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c7 : ∀ l : Fin Nat4, 280 ≤ l.val → l.val < 320 → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
set_option maxHeartbeats 0 in
theorem hcoef4_c8 : ∀ l : Fin Nat4, 320 ≤ l.val → D14 l - D24 l = D34 l - (D44 l - D54 l) := by decide +kernel
/-- The pointwise coefficient identity of the collar of cusp `4`. -/
theorem hcoef4 : ∀ l : Fin Nat4, D14 l - D24 l = D34 l - (D44 l - D54 l) := by
  intro l
  by_cases h0 : l.val < 40
  · exact hcoef4_c0 l (by omega) h0
  by_cases h1 : l.val < 80
  · exact hcoef4_c1 l (by omega) h1
  by_cases h2 : l.val < 120
  · exact hcoef4_c2 l (by omega) h2
  by_cases h3 : l.val < 160
  · exact hcoef4_c3 l (by omega) h3
  by_cases h4 : l.val < 200
  · exact hcoef4_c4 l (by omega) h4
  by_cases h5 : l.val < 240
  · exact hcoef4_c5 l (by omega) h5
  by_cases h6 : l.val < 280
  · exact hcoef4_c6 l (by omega) h6
  by_cases h7 : l.val < 320
  · exact hcoef4_c7 l (by omega) h7
  exact hcoef4_c8 l (by omega)

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


end

end Work.BridgeSquare.SlabBuild

