import Mathlib
import Submission.Work.BridgeSquare.SlabCore

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.BridgeSquare.WallCollar

open Convexity
open Work.Subdivision
open Work.MbarHomology

noncomputable section

/-! ## The wall chains and the collar chains, per cusp

`tauV` is the *untranslated* triangle (in the slab coordinates `slabPt y₀ y₁ 1`), `lamV` the
lattice translation that brings the square of the triangle into the standard block; the wall
chain uses the translated triangles `tauV v j + lamV v j`, which have the same `cChain` by
`PlaneSlab.cChain_add_lattice`.

The collar pieces `colTri`/`colLam`/`colCoef` are the explicit solution of
`dLC 1 K = dLC 1 W - dLC 1 slabBot` with `K = Σ colCoef • (![colTri] - ![colTri + colLam])`.
-/

/-- The number of wall triangles of cusp `0`. -/
abbrev Idx0 : Type := Fin 32

/-- The cell of `C_2(Gen.mbarCx)` of the `j`-th wall triangle of cusp `0`. -/
def cellV0 : Idx0 → Fin 192 := ![152, 152, 152, 152, 152, 152, 152, 152, 158, 158, 158, 158, 158, 158, 158, 158, 22, 22, 22, 22, 22, 22, 22, 22, 16, 16, 16, 16, 16, 16, 16, 16]

/-- The cube carrying the `j`-th wall triangle of cusp `0`. -/
def cubeV0 : Idx0 → Fin 48 := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]

/-- The (untranslated) wall triangle, in the slab coordinates. -/
def tauV0 : Idx0 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1]
]

/-- The lattice translation bringing the square into the standard block. -/
def lamV0 : Idx0 → CuspE3 := ![slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0]

/-- The coefficient of the `j`-th wall triangle of cusp `0`. -/
def coefV0 : Idx0 → ℤ := ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]

/-- The wall chain of cusp `0`: the barycentric subdivision of the wall, in the standard block. -/
def wallChain0 : AffC 2 :=
  ∑ j : Idx0, coefV0 j • Finsupp.single (fun i => tauV0 j i + lamV0 j) (1 : ℤ)

/-- The number of collar pieces of cusp `0`. -/
abbrev NCol0 : Type := Fin 24

/-- The triangles of the collar of cusp `0`. -/
def colTri0 : NCol0 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (0) 1, slabPt (-3/4) (1/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (1/4) 1, slabPt (-3/4) (0) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (1/4) (-3/4) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (1/4) (-3/4) 1, slabPt (0) (-3/4) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (0) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (0) 1, slabPt (0) (0) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (-3/4) 1, slabPt (0) (0) 0, slabPt (1/4) (-3/4) 1],
  ![slabPt (0) (0) 0, slabPt (0) (1) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (0) 0, slabPt (1) (0) 0, slabPt (1/4) (-3/4) 1]
]

/-- The translations of the collar pieces of cusp `0`. -/
def colLam0 : NCol0 → CuspE3 := ![slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0]

/-- The coefficients of the collar pieces of cusp `0`. -/
def colCoef0 : NCol0 → ℤ := ![-1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1]

/-- The collar chain of cusp `0`: a sum of `Λ`-translate differences, hence in the
kernel of `slabChain v 2` (by `PlaneSlab.slabChain_translate_sub`). -/
def collarChain0 : AffC 2 :=
  ∑ j : NCol0, colCoef0 j •
    (Finsupp.single (colTri0 j) (1 : ℤ)
      - Finsupp.single (fun i => colTri0 j i + colLam0 j) (1 : ℤ))

/-- The number of wall triangles of cusp `1`. -/
abbrev Idx1 : Type := Fin 32

/-- The cell of `C_2(Gen.mbarCx)` of the `j`-th wall triangle of cusp `1`. -/
def cellV1 : Idx1 → Fin 192 := ![141, 141, 141, 141, 141, 141, 141, 141, 11, 11, 11, 11, 11, 11, 11, 11, 147, 147, 147, 147, 147, 147, 147, 147, 5, 5, 5, 5, 5, 5, 5, 5]

/-- The cube carrying the `j`-th wall triangle of cusp `1`. -/
def cubeV1 : Idx1 → Fin 48 := ![4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7]

/-- The (untranslated) wall triangle, in the slab coordinates. -/
def tauV1 : Idx1 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1]
]

/-- The lattice translation bringing the square into the standard block. -/
def lamV1 : Idx1 → CuspE3 := ![slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0]

/-- The coefficient of the `j`-th wall triangle of cusp `1`. -/
def coefV1 : Idx1 → ℤ := ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]

/-- The wall chain of cusp `1`: the barycentric subdivision of the wall, in the standard block. -/
def wallChain1 : AffC 2 :=
  ∑ j : Idx1, coefV1 j • Finsupp.single (fun i => tauV1 j i + lamV1 j) (1 : ℤ)

/-- The number of collar pieces of cusp `1`. -/
abbrev NCol1 : Type := Fin 24

/-- The triangles of the collar of cusp `1`. -/
def colTri1 : NCol1 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (0) 1, slabPt (-3/4) (1/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (1/4) 1, slabPt (-3/4) (0) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (1/4) (-3/4) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (1/4) (-3/4) 1, slabPt (0) (-3/4) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (0) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (0) 1, slabPt (0) (0) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (-3/4) 1, slabPt (0) (0) 0, slabPt (1/4) (-3/4) 1],
  ![slabPt (0) (0) 0, slabPt (0) (1) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (0) 0, slabPt (1) (0) 0, slabPt (1/4) (-3/4) 1]
]

/-- The translations of the collar pieces of cusp `1`. -/
def colLam1 : NCol1 → CuspE3 := ![slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0]

/-- The coefficients of the collar pieces of cusp `1`. -/
def colCoef1 : NCol1 → ℤ := ![-1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1]

/-- The collar chain of cusp `1`: a sum of `Λ`-translate differences, hence in the
kernel of `slabChain v 2` (by `PlaneSlab.slabChain_translate_sub`). -/
def collarChain1 : AffC 2 :=
  ∑ j : NCol1, colCoef1 j •
    (Finsupp.single (colTri1 j) (1 : ℤ)
      - Finsupp.single (fun i => colTri1 j i + colLam1 j) (1 : ℤ))

/-- The number of wall triangles of cusp `2`. -/
abbrev Idx2 : Type := Fin 32

/-- The cell of `C_2(Gen.mbarCx)` of the `j`-th wall triangle of cusp `2`. -/
def cellV2 : Idx2 → Fin 192 := ![176, 176, 176, 176, 176, 176, 176, 176, 182, 182, 182, 182, 182, 182, 182, 182, 94, 94, 94, 94, 94, 94, 94, 94, 88, 88, 88, 88, 88, 88, 88, 88]

/-- The cube carrying the `j`-th wall triangle of cusp `2`. -/
def cubeV2 : Idx2 → Fin 48 := ![8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11]

/-- The (untranslated) wall triangle, in the slab coordinates. -/
def tauV2 : Idx2 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1]
]

/-- The lattice translation bringing the square into the standard block. -/
def lamV2 : Idx2 → CuspE3 := ![slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0]

/-- The coefficient of the `j`-th wall triangle of cusp `2`. -/
def coefV2 : Idx2 → ℤ := ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]

/-- The wall chain of cusp `2`: the barycentric subdivision of the wall, in the standard block. -/
def wallChain2 : AffC 2 :=
  ∑ j : Idx2, coefV2 j • Finsupp.single (fun i => tauV2 j i + lamV2 j) (1 : ℤ)

/-- The number of collar pieces of cusp `2`. -/
abbrev NCol2 : Type := Fin 24

/-- The triangles of the collar of cusp `2`. -/
def colTri2 : NCol2 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (0) 1, slabPt (-3/4) (1/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (1/4) 1, slabPt (-3/4) (0) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (1/4) (-3/4) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (1/4) (-3/4) 1, slabPt (0) (-3/4) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (0) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (0) 1, slabPt (0) (0) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (-3/4) 1, slabPt (0) (0) 0, slabPt (1/4) (-3/4) 1],
  ![slabPt (0) (0) 0, slabPt (0) (1) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (0) 0, slabPt (1) (0) 0, slabPt (1/4) (-3/4) 1]
]

/-- The translations of the collar pieces of cusp `2`. -/
def colLam2 : NCol2 → CuspE3 := ![slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0]

/-- The coefficients of the collar pieces of cusp `2`. -/
def colCoef2 : NCol2 → ℤ := ![-1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1]

/-- The collar chain of cusp `2`: a sum of `Λ`-translate differences, hence in the
kernel of `slabChain v 2` (by `PlaneSlab.slabChain_translate_sub`). -/
def collarChain2 : AffC 2 :=
  ∑ j : NCol2, colCoef2 j •
    (Finsupp.single (colTri2 j) (1 : ℤ)
      - Finsupp.single (fun i => colTri2 j i + colLam2 j) (1 : ℤ))

/-- The number of wall triangles of cusp `3`. -/
abbrev Idx3 : Type := Fin 32

/-- The cell of `C_2(Gen.mbarCx)` of the `j`-th wall triangle of cusp `3`. -/
def cellV3 : Idx3 → Fin 192 := ![165, 165, 165, 165, 165, 165, 165, 165, 83, 83, 83, 83, 83, 83, 83, 83, 171, 171, 171, 171, 171, 171, 171, 171, 77, 77, 77, 77, 77, 77, 77, 77]

/-- The cube carrying the `j`-th wall triangle of cusp `3`. -/
def cubeV3 : Idx3 → Fin 48 := ![12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15]

/-- The (untranslated) wall triangle, in the slab coordinates. -/
def tauV3 : Idx3 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (-3/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/2) (3/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-3/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/2) (1/4) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-3/4) (1/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1],
  ![slabPt (-3/4) (3/4) 1, slabPt (-3/4) (1/2) 1, slabPt (-1/2) (1/2) 1]
]

/-- The lattice translation bringing the square into the standard block. -/
def lamV3 : Idx3 → CuspE3 := ![slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0]

/-- The coefficient of the `j`-th wall triangle of cusp `3`. -/
def coefV3 : Idx3 → ℤ := ![-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]

/-- The wall chain of cusp `3`: the barycentric subdivision of the wall, in the standard block. -/
def wallChain3 : AffC 2 :=
  ∑ j : Idx3, coefV3 j • Finsupp.single (fun i => tauV3 j i + lamV3 j) (1 : ℤ)

/-- The number of collar pieces of cusp `3`. -/
abbrev NCol3 : Type := Fin 24

/-- The triangles of the collar of cusp `3`. -/
def colTri3 : NCol3 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-1/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-1/2) (-3/4) 1],
  ![slabPt (-1/2) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-1/2) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-1/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (0) (0) 0, slabPt (-3/4) (-3/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (0) 1, slabPt (-3/4) (1/4) 1],
  ![slabPt (-1/2) (0) 1, slabPt (-3/4) (1/4) 1, slabPt (-3/4) (0) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-1/4) (-3/4) 1, slabPt (0) (-3/4) 1, slabPt (1/4) (-3/4) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (1/4) (-3/4) 1, slabPt (0) (-3/4) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-1/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-3/4) (-3/4) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-3/4) (0) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (0) 1, slabPt (0) (0) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (-3/4) 1, slabPt (0) (0) 0, slabPt (1/4) (-3/4) 1],
  ![slabPt (0) (0) 0, slabPt (0) (1) 0, slabPt (-3/4) (1/4) 1],
  ![slabPt (0) (0) 0, slabPt (1) (0) 0, slabPt (1/4) (-3/4) 1]
]

/-- The translations of the collar pieces of cusp `3`. -/
def colLam3 : NCol3 → CuspE3 := ![slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0]

/-- The coefficients of the collar pieces of cusp `3`. -/
def colCoef3 : NCol3 → ℤ := ![-1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1]

/-- The collar chain of cusp `3`: a sum of `Λ`-translate differences, hence in the
kernel of `slabChain v 2` (by `PlaneSlab.slabChain_translate_sub`). -/
def collarChain3 : AffC 2 :=
  ∑ j : NCol3, colCoef3 j •
    (Finsupp.single (colTri3 j) (1 : ℤ)
      - Finsupp.single (fun i => colTri3 j i + colLam3 j) (1 : ℤ))

/-- The number of wall triangles of cusp `4`. -/
abbrev Idx4 : Type := Fin 128

/-- The cell of `C_2(Gen.mbarCx)` of the `j`-th wall triangle of cusp `4`. -/
def cellV4 : Idx4 → Fin 192 := ![27, 27, 27, 27, 27, 27, 27, 27, 25, 25, 25, 25, 25, 25, 25, 25, 39, 39, 39, 39, 39, 39, 39, 39, 33, 33, 33, 33, 33, 33, 33, 33, 26, 26, 26, 26, 26, 26, 26, 26, 37, 37, 37, 37, 37, 37, 37, 37, 31, 31, 31, 31, 31, 31, 31, 31, 24, 24, 24, 24, 24, 24, 24, 24, 45, 45, 45, 45, 45, 45, 45, 45, 38, 38, 38, 38, 38, 38, 38, 38, 32, 32, 32, 32, 32, 32, 32, 32, 43, 43, 43, 43, 43, 43, 43, 43, 36, 36, 36, 36, 36, 36, 36, 36, 30, 30, 30, 30, 30, 30, 30, 30, 44, 44, 44, 44, 44, 44, 44, 44, 42, 42, 42, 42, 42, 42, 42, 42]

/-- The cube carrying the `j`-th wall triangle of cusp `4`. -/
def cubeV4 : Idx4 → Fin 48 := ![16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 31, 31, 31, 31, 31, 31, 31, 31, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 37, 37, 37, 37, 37, 37, 37, 37, 40, 40, 40, 40, 40, 40, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44]

/-- The (untranslated) wall triangle, in the slab coordinates. -/
def tauV4 : Idx4 → Fin 3 → CuspE3 := ![
  ![slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1],
  ![slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1],
  ![slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1],
  ![slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1],
  ![slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1],
  ![slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1],
  ![slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1],
  ![slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1],
  ![slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1],
  ![slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1],
  ![slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1],
  ![slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1],
  ![slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1],
  ![slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1],
  ![slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1],
  ![slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1],
  ![slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1],
  ![slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1],
  ![slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1],
  ![slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1]
]

/-- The lattice translation bringing the square into the standard block. -/
def lamV4 : Idx4 → CuspE3 := ![slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (0) (0) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (0) (-1) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (0) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0, slabPt (-1) (-1) 0]

/-- The coefficient of the `j`-th wall triangle of cusp `4`. -/
def coefV4 : Idx4 → ℤ := ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1]

/-- The wall chain of cusp `4`: the barycentric subdivision of the wall, in the standard block. -/
def wallChain4 : AffC 2 :=
  ∑ j : Idx4, coefV4 j • Finsupp.single (fun i => tauV4 j i + lamV4 j) (1 : ℤ)

/-- The number of collar pieces of cusp `4`. -/
abbrev NCol4 : Type := Fin 48

/-- The triangles of the collar of cusp `4`. -/
def colTri4 : NCol4 → Fin 3 → CuspE3 := ![
  ![slabPt (-1/2) (-3/4) 1, slabPt (-1/2) (-7/8) 1, slabPt (-3/8) (-7/8) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-1/2) (-7/8) 1, slabPt (-5/8) (-7/8) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-3/8) (-7/8) 1, slabPt (-1/2) (-7/8) 1],
  ![slabPt (-1/2) (-3/4) 1, slabPt (-5/8) (-7/8) 1, slabPt (-1/2) (-7/8) 1],
  ![slabPt (-1/2) (-7/8) 1, slabPt (-3/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-1/2) (-7/8) 1, slabPt (-5/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-1/4) (-3/4) 1, slabPt (-1/4) (-7/8) 1, slabPt (-1/8) (-7/8) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (-1/4) (-7/8) 1, slabPt (-3/8) (-7/8) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (-1/8) (-7/8) 1, slabPt (-1/4) (-7/8) 1],
  ![slabPt (-1/4) (-3/4) 1, slabPt (-3/8) (-7/8) 1, slabPt (-1/4) (-7/8) 1],
  ![slabPt (-1/4) (-7/8) 1, slabPt (-1/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-1/4) (-7/8) 1, slabPt (-3/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-1/8) (-7/8) 1, slabPt (0) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-1/8) (-7/8) 1, slabPt (0) (-7/8) 1, slabPt (1/8) (-7/8) 1],
  ![slabPt (-1/8) (-7/8) 1, slabPt (1/8) (-7/8) 1, slabPt (0) (-7/8) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-1/2) 1, slabPt (-7/8) (-3/8) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-1/2) 1, slabPt (-7/8) (-5/8) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-3/8) 1, slabPt (-7/8) (-1/2) 1],
  ![slabPt (-3/4) (-1/2) 1, slabPt (-7/8) (-5/8) 1, slabPt (-7/8) (-1/2) 1],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-1/4) 1, slabPt (-7/8) (-1/8) 1],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-1/4) 1, slabPt (-7/8) (-3/8) 1],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-1/8) 1, slabPt (-7/8) (-1/4) 1],
  ![slabPt (-3/4) (-1/4) 1, slabPt (-7/8) (-3/8) 1, slabPt (-7/8) (-1/4) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-7/8) 1, slabPt (-5/8) (-7/8) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-3/4) (-7/8) 1, slabPt (-7/8) (-7/8) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-5/8) (-7/8) 1, slabPt (-3/4) (-7/8) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-3/4) 1, slabPt (-7/8) (-5/8) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-3/4) 1, slabPt (-7/8) (-7/8) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-5/8) 1, slabPt (-7/8) (-3/4) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-7/8) 1, slabPt (-3/4) (-7/8) 1],
  ![slabPt (-3/4) (-3/4) 1, slabPt (-7/8) (-7/8) 1, slabPt (-7/8) (-3/4) 1],
  ![slabPt (-3/4) (-7/8) 1, slabPt (-5/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-7/8) 1, slabPt (-7/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-3/4) (-7/8) 1, slabPt (0) (0) 0, slabPt (-7/8) (-7/8) 1],
  ![slabPt (-3/4) (-7/8) 1, slabPt (0) (0) 0, slabPt (-7/8) (-7/8) 1],
  ![slabPt (-3/4) (0) 1, slabPt (-7/8) (0) 1, slabPt (-7/8) (1/8) 1],
  ![slabPt (-3/4) (0) 1, slabPt (-7/8) (1/8) 1, slabPt (-7/8) (0) 1],
  ![slabPt (-7/8) (-1/2) 1, slabPt (-7/8) (-3/8) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (-1/2) 1, slabPt (-7/8) (-5/8) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (-1/4) 1, slabPt (-7/8) (-1/8) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (-1/4) 1, slabPt (-7/8) (-3/8) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (-1/8) 1, slabPt (-7/8) (0) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (-3/4) 1, slabPt (-7/8) (-5/8) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (-3/4) 1, slabPt (-7/8) (-7/8) 1, slabPt (0) (0) 0],
  ![slabPt (-7/8) (0) 1, slabPt (0) (0) 0, slabPt (-7/8) (1/8) 1],
  ![slabPt (0) (-7/8) 1, slabPt (0) (0) 0, slabPt (1/8) (-7/8) 1],
  ![slabPt (0) (0) 0, slabPt (0) (1) 0, slabPt (-7/8) (1/8) 1],
  ![slabPt (0) (0) 0, slabPt (1) (0) 0, slabPt (1/8) (-7/8) 1]
]

/-- The translations of the collar pieces of cusp `4`. -/
def colLam4 : NCol4 → CuspE3 := ![slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (1) (0) 0, slabPt (0) (1) 0, slabPt (1) (0) 0, slabPt (0) (1) 0]

/-- The coefficients of the collar pieces of cusp `4`. -/
def colCoef4 : NCol4 → ℤ := ![-1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1]

/-- The collar chain of cusp `4`: a sum of `Λ`-translate differences, hence in the
kernel of `slabChain v 2` (by `PlaneSlab.slabChain_translate_sub`). -/
def collarChain4 : AffC 2 :=
  ∑ j : NCol4, colCoef4 j •
    (Finsupp.single (colTri4 j) (1 : ℤ)
      - Finsupp.single (fun i => colTri4 j i + colLam4 j) (1 : ℤ))

/-- Coordinatewise addition of slab points. -/
theorem slabPt_add' (a b c d e f : ℝ) :
    slabPt a b c + slabPt d e f = slabPt (a + d) (b + e) (c + f) := by
  apply PiLp.ext
  intro m
  fin_cases m <;> simp [slabPt]

end

end Work.BridgeSquare.WallCollar
