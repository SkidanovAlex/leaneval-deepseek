import Mathlib
import Submission.Work.BridgeSquare.SlabCore
import Submission.Work.BridgeSquare.denseSimplex3
import Submission.Work.BridgeSquare.Psi1Defs

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

namespace Work.BridgeSquare.SlabBuild

open Convexity
open Work.Subdivision
open Work.MbarHomology

noncomputable section

/-! ## The nice flags of the wall triangles -/

/-- The flag `(846 < 204 < 31)` of `Q̄`. -/
def fl_1_4_846_204 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨846⟩ : QbarCell)) (⟨204⟩ : QbarCell)
      (fun _ => show (⟨846⟩ : QbarCell) < (⟨204⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨846⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨846⟩ : QbarCell) < (⟨204⟩ : QbarCell) from by decide +kernel) (show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(858 < 204 < 31)` of `Q̄`. -/
def fl_1_4_858_204 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨858⟩ : QbarCell)) (⟨204⟩ : QbarCell)
      (fun _ => show (⟨858⟩ : QbarCell) < (⟨204⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨858⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨858⟩ : QbarCell) < (⟨204⟩ : QbarCell) from by decide +kernel) (show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(816 < 208 < 31)` of `Q̄`. -/
def fl_1_4_816_208 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨816⟩ : QbarCell)) (⟨208⟩ : QbarCell)
      (fun _ => show (⟨816⟩ : QbarCell) < (⟨208⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨816⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨816⟩ : QbarCell) < (⟨208⟩ : QbarCell) from by decide +kernel) (show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(831 < 208 < 31)` of `Q̄`. -/
def fl_1_4_831_208 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨831⟩ : QbarCell)) (⟨208⟩ : QbarCell)
      (fun _ => show (⟨831⟩ : QbarCell) < (⟨208⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨831⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨831⟩ : QbarCell) < (⟨208⟩ : QbarCell) from by decide +kernel) (show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(831 < 220 < 31)` of `Q̄`. -/
def fl_1_4_831_220 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨831⟩ : QbarCell)) (⟨220⟩ : QbarCell)
      (fun _ => show (⟨831⟩ : QbarCell) < (⟨220⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨831⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨831⟩ : QbarCell) < (⟨220⟩ : QbarCell) from by decide +kernel) (show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(858 < 220 < 31)` of `Q̄`. -/
def fl_1_4_858_220 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨858⟩ : QbarCell)) (⟨220⟩ : QbarCell)
      (fun _ => show (⟨858⟩ : QbarCell) < (⟨220⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨858⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨858⟩ : QbarCell) < (⟨220⟩ : QbarCell) from by decide +kernel) (show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(816 < 224 < 31)` of `Q̄`. -/
def fl_1_4_816_224 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨816⟩ : QbarCell)) (⟨224⟩ : QbarCell)
      (fun _ => show (⟨816⟩ : QbarCell) < (⟨224⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨816⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨816⟩ : QbarCell) < (⟨224⟩ : QbarCell) from by decide +kernel) (show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(846 < 224 < 31)` of `Q̄`. -/
def fl_1_4_846_224 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨846⟩ : QbarCell)) (⟨224⟩ : QbarCell)
      (fun _ => show (⟨846⟩ : QbarCell) < (⟨224⟩ : QbarCell) from by decide +kernel))
    (⟨31⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨846⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨846⟩ : QbarCell) < (⟨224⟩ : QbarCell) from by decide +kernel) (show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)

/-- The flag `(636 < 300 < 52)` of `Q̄`. -/
def fl_1_5_636_300 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨636⟩ : QbarCell)) (⟨300⟩ : QbarCell)
      (fun _ => show (⟨636⟩ : QbarCell) < (⟨300⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨636⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨636⟩ : QbarCell) < (⟨300⟩ : QbarCell) from by decide +kernel) (show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(654 < 300 < 52)` of `Q̄`. -/
def fl_1_5_654_300 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨654⟩ : QbarCell)) (⟨300⟩ : QbarCell)
      (fun _ => show (⟨654⟩ : QbarCell) < (⟨300⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨654⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨654⟩ : QbarCell) < (⟨300⟩ : QbarCell) from by decide +kernel) (show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(594 < 304 < 52)` of `Q̄`. -/
def fl_1_5_594_304 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨594⟩ : QbarCell)) (⟨304⟩ : QbarCell)
      (fun _ => show (⟨594⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨594⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨594⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel) (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(615 < 304 < 52)` of `Q̄`. -/
def fl_1_5_615_304 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨615⟩ : QbarCell)) (⟨304⟩ : QbarCell)
      (fun _ => show (⟨615⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨615⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨615⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel) (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(615 < 316 < 52)` of `Q̄`. -/
def fl_1_5_615_316 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨615⟩ : QbarCell)) (⟨316⟩ : QbarCell)
      (fun _ => show (⟨615⟩ : QbarCell) < (⟨316⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨615⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨615⟩ : QbarCell) < (⟨316⟩ : QbarCell) from by decide +kernel) (show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(654 < 316 < 52)` of `Q̄`. -/
def fl_1_5_654_316 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨654⟩ : QbarCell)) (⟨316⟩ : QbarCell)
      (fun _ => show (⟨654⟩ : QbarCell) < (⟨316⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨654⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨654⟩ : QbarCell) < (⟨316⟩ : QbarCell) from by decide +kernel) (show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨316⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(594 < 320 < 52)` of `Q̄`. -/
def fl_1_5_594_320 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨594⟩ : QbarCell)) (⟨320⟩ : QbarCell)
      (fun _ => show (⟨594⟩ : QbarCell) < (⟨320⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨594⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨594⟩ : QbarCell) < (⟨320⟩ : QbarCell) from by decide +kernel) (show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(636 < 320 < 52)` of `Q̄`. -/
def fl_1_5_636_320 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨636⟩ : QbarCell)) (⟨320⟩ : QbarCell)
      (fun _ => show (⟨636⟩ : QbarCell) < (⟨320⟩ : QbarCell) from by decide +kernel))
    (⟨52⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨636⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨636⟩ : QbarCell) < (⟨320⟩ : QbarCell) from by decide +kernel) (show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨320⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)

/-- The flag `(783 < 268 < 45)` of `Q̄`. -/
def fl_1_6_783_268 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨783⟩ : QbarCell)) (⟨268⟩ : QbarCell)
      (fun _ => show (⟨783⟩ : QbarCell) < (⟨268⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨783⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨783⟩ : QbarCell) < (⟨268⟩ : QbarCell) from by decide +kernel) (show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(798 < 268 < 45)` of `Q̄`. -/
def fl_1_6_798_268 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨798⟩ : QbarCell)) (⟨268⟩ : QbarCell)
      (fun _ => show (⟨798⟩ : QbarCell) < (⟨268⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨798⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨798⟩ : QbarCell) < (⟨268⟩ : QbarCell) from by decide +kernel) (show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨268⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(747 < 272 < 45)` of `Q̄`. -/
def fl_1_6_747_272 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨747⟩ : QbarCell)) (⟨272⟩ : QbarCell)
      (fun _ => show (⟨747⟩ : QbarCell) < (⟨272⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨747⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨747⟩ : QbarCell) < (⟨272⟩ : QbarCell) from by decide +kernel) (show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(765 < 272 < 45)` of `Q̄`. -/
def fl_1_6_765_272 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨765⟩ : QbarCell)) (⟨272⟩ : QbarCell)
      (fun _ => show (⟨765⟩ : QbarCell) < (⟨272⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨765⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨765⟩ : QbarCell) < (⟨272⟩ : QbarCell) from by decide +kernel) (show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨272⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(765 < 284 < 45)` of `Q̄`. -/
def fl_1_6_765_284 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨765⟩ : QbarCell)) (⟨284⟩ : QbarCell)
      (fun _ => show (⟨765⟩ : QbarCell) < (⟨284⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨765⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨765⟩ : QbarCell) < (⟨284⟩ : QbarCell) from by decide +kernel) (show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(798 < 284 < 45)` of `Q̄`. -/
def fl_1_6_798_284 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨798⟩ : QbarCell)) (⟨284⟩ : QbarCell)
      (fun _ => show (⟨798⟩ : QbarCell) < (⟨284⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨798⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨798⟩ : QbarCell) < (⟨284⟩ : QbarCell) from by decide +kernel) (show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨284⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(747 < 288 < 45)` of `Q̄`. -/
def fl_1_6_747_288 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨747⟩ : QbarCell)) (⟨288⟩ : QbarCell)
      (fun _ => show (⟨747⟩ : QbarCell) < (⟨288⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨747⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨747⟩ : QbarCell) < (⟨288⟩ : QbarCell) from by decide +kernel) (show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(783 < 288 < 45)` of `Q̄`. -/
def fl_1_6_783_288 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨783⟩ : QbarCell)) (⟨288⟩ : QbarCell)
      (fun _ => show (⟨783⟩ : QbarCell) < (⟨288⟩ : QbarCell) from by decide +kernel))
    (⟨45⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨783⟩ : QbarCell) < (⟨45⟩ : QbarCell) from lt_trans (show (⟨783⟩ : QbarCell) < (⟨288⟩ : QbarCell) from by decide +kernel) (show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨288⟩ : QbarCell) < (⟨45⟩ : QbarCell) from by decide +kernel)

/-- The flag `(711 < 236 < 38)` of `Q̄`. -/
def fl_1_7_711_236 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨711⟩ : QbarCell)) (⟨236⟩ : QbarCell)
      (fun _ => show (⟨711⟩ : QbarCell) < (⟨236⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨711⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨711⟩ : QbarCell) < (⟨236⟩ : QbarCell) from by decide +kernel) (show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(726 < 236 < 38)` of `Q̄`. -/
def fl_1_7_726_236 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨726⟩ : QbarCell)) (⟨236⟩ : QbarCell)
      (fun _ => show (⟨726⟩ : QbarCell) < (⟨236⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨726⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨726⟩ : QbarCell) < (⟨236⟩ : QbarCell) from by decide +kernel) (show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨236⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(675 < 240 < 38)` of `Q̄`. -/
def fl_1_7_675_240 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨675⟩ : QbarCell)) (⟨240⟩ : QbarCell)
      (fun _ => show (⟨675⟩ : QbarCell) < (⟨240⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨675⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨675⟩ : QbarCell) < (⟨240⟩ : QbarCell) from by decide +kernel) (show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(693 < 240 < 38)` of `Q̄`. -/
def fl_1_7_693_240 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨693⟩ : QbarCell)) (⟨240⟩ : QbarCell)
      (fun _ => show (⟨693⟩ : QbarCell) < (⟨240⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨693⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨693⟩ : QbarCell) < (⟨240⟩ : QbarCell) from by decide +kernel) (show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨240⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(693 < 252 < 38)` of `Q̄`. -/
def fl_1_7_693_252 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨693⟩ : QbarCell)) (⟨252⟩ : QbarCell)
      (fun _ => show (⟨693⟩ : QbarCell) < (⟨252⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨693⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨693⟩ : QbarCell) < (⟨252⟩ : QbarCell) from by decide +kernel) (show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(726 < 252 < 38)` of `Q̄`. -/
def fl_1_7_726_252 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨726⟩ : QbarCell)) (⟨252⟩ : QbarCell)
      (fun _ => show (⟨726⟩ : QbarCell) < (⟨252⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨726⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨726⟩ : QbarCell) < (⟨252⟩ : QbarCell) from by decide +kernel) (show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨252⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(675 < 256 < 38)` of `Q̄`. -/
def fl_1_7_675_256 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨675⟩ : QbarCell)) (⟨256⟩ : QbarCell)
      (fun _ => show (⟨675⟩ : QbarCell) < (⟨256⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨675⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨675⟩ : QbarCell) < (⟨256⟩ : QbarCell) from by decide +kernel) (show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-- The flag `(711 < 256 < 38)` of `Q̄`. -/
def fl_1_7_711_256 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨711⟩ : QbarCell)) (⟨256⟩ : QbarCell)
      (fun _ => show (⟨711⟩ : QbarCell) < (⟨256⟩ : QbarCell) from by decide +kernel))
    (⟨38⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨711⟩ : QbarCell) < (⟨38⟩ : QbarCell) from lt_trans (show (⟨711⟩ : QbarCell) < (⟨256⟩ : QbarCell) from by decide +kernel) (show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨256⟩ : QbarCell) < (⟨38⟩ : QbarCell) from by decide +kernel)

/-! ## The leaf points of the wall squares -/

/-- Leaf `31` of the square `4` of cusp `1`. -/
theorem leaf_1_4_31 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (31 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `204` of the square `4` of cusp `1`. -/
theorem leaf_1_4_204 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (204 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `208` of the square `4` of cusp `1`. -/
theorem leaf_1_4_208 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (208 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `220` of the square `4` of cusp `1`. -/
theorem leaf_1_4_220 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (220 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `224` of the square `4` of cusp `1`. -/
theorem leaf_1_4_224 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (224 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `816` of the square `4` of cusp `1`. -/
theorem leaf_1_4_816 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (816 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `831` of the square `4` of cusp `1`. -/
theorem leaf_1_4_831 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (831 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `846` of the square `4` of cusp `1`. -/
theorem leaf_1_4_846 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (846 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `858` of the square `4` of cusp `1`. -/
theorem leaf_1_4_858 :
    Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (858 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `52` of the square `5` of cusp `1`. -/
theorem leaf_1_5_52 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (52 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `300` of the square `5` of cusp `1`. -/
theorem leaf_1_5_300 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (300 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `304` of the square `5` of cusp `1`. -/
theorem leaf_1_5_304 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (304 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `316` of the square `5` of cusp `1`. -/
theorem leaf_1_5_316 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (316 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `320` of the square `5` of cusp `1`. -/
theorem leaf_1_5_320 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (320 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `594` of the square `5` of cusp `1`. -/
theorem leaf_1_5_594 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (594 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `615` of the square `5` of cusp `1`. -/
theorem leaf_1_5_615 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (615 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `636` of the square `5` of cusp `1`. -/
theorem leaf_1_5_636 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (636 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `654` of the square `5` of cusp `1`. -/
theorem leaf_1_5_654 :
    Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (654 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `45` of the square `6` of cusp `1`. -/
theorem leaf_1_6_45 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (45 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `268` of the square `6` of cusp `1`. -/
theorem leaf_1_6_268 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (268 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `272` of the square `6` of cusp `1`. -/
theorem leaf_1_6_272 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (272 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `284` of the square `6` of cusp `1`. -/
theorem leaf_1_6_284 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (284 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `288` of the square `6` of cusp `1`. -/
theorem leaf_1_6_288 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (288 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `747` of the square `6` of cusp `1`. -/
theorem leaf_1_6_747 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (747 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `765` of the square `6` of cusp `1`. -/
theorem leaf_1_6_765 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (765 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `783` of the square `6` of cusp `1`. -/
theorem leaf_1_6_783 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (783 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `798` of the square `6` of cusp `1`. -/
theorem leaf_1_6_798 :
    Work.RTOwed.kleinPt 6 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (798 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `38` of the square `7` of cusp `1`. -/
theorem leaf_1_7_38 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (38 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `236` of the square `7` of cusp `1`. -/
theorem leaf_1_7_236 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (236 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `240` of the square `7` of cusp `1`. -/
theorem leaf_1_7_240 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (240 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `252` of the square `7` of cusp `1`. -/
theorem leaf_1_7_252 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (252 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `256` of the square `7` of cusp `1`. -/
theorem leaf_1_7_256 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (256 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `675` of the square `7` of cusp `1`. -/
theorem leaf_1_7_675 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (675 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `693` of the square `7` of cusp `1`. -/
theorem leaf_1_7_693 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (693 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `711` of the square `7` of cusp `1`. -/
theorem leaf_1_7_711 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-3/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (711 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `726` of the square `7` of cusp `1`. -/
theorem leaf_1_7_726 :
    Work.RTOwed.kleinPt 7 (slabL 1 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (726 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- The chart identity of the flag `(846,204,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_846_204 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_204))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_846_204 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (846 : Fin 865)
      exact leaf_1_4_846
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (204 : Fin 865)
      exact leaf_1_4_204
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_1_4_846_204 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_846_204) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_846_204)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_204) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_846_204
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨846⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨846⟩ : QbarCell) < (⟨204⟩ : QbarCell) from by decide +kernel) (show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_204))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_204) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_204) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(858,204,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_858_204 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_204))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_858_204 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (858 : Fin 865)
      exact leaf_1_4_858
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (204 : Fin 865)
      exact leaf_1_4_204
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_1_4_858_204 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_858_204) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_858_204)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_204) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_858_204
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨858⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨858⟩ : QbarCell) < (⟨204⟩ : QbarCell) from by decide +kernel) (show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨204⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_204))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_204) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_204) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(816,208,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_816_208 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_208))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_816_208 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (816 : Fin 865)
      exact leaf_1_4_816
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (208 : Fin 865)
      exact leaf_1_4_208
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_1_4_816_208 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_816_208) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_816_208)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_208) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_816_208
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨816⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨816⟩ : QbarCell) < (⟨208⟩ : QbarCell) from by decide +kernel) (show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_208))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_208) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_208) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(831,208,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_831_208 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_208))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_831_208 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (831 : Fin 865)
      exact leaf_1_4_831
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (208 : Fin 865)
      exact leaf_1_4_208
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_1_4_831_208 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_831_208) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_831_208)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_208) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_831_208
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨831⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨831⟩ : QbarCell) < (⟨208⟩ : QbarCell) from by decide +kernel) (show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨208⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_208))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_208) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_208) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(831,220,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_831_220 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_220))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_831_220 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (831 : Fin 865)
      exact leaf_1_4_831
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (220 : Fin 865)
      exact leaf_1_4_220
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_1_4_831_220 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_831_220) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_831_220)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_220) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_831_220
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨831⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨831⟩ : QbarCell) < (⟨220⟩ : QbarCell) from by decide +kernel) (show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_220))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_220) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_831_220) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(858,220,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_858_220 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_220))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_858_220 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (858 : Fin 865)
      exact leaf_1_4_858
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (220 : Fin 865)
      exact leaf_1_4_220
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_1_4_858_220 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_858_220) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_858_220)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_220) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_858_220
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨858⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨858⟩ : QbarCell) < (⟨220⟩ : QbarCell) from by decide +kernel) (show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨220⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_220))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_220) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_858_220) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(816,224,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_816_224 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_224))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_816_224 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (816 : Fin 865)
      exact leaf_1_4_816
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (224 : Fin 865)
      exact leaf_1_4_224
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_1_4_816_224 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_816_224) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_816_224)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_224) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_816_224
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨816⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨816⟩ : QbarCell) < (⟨224⟩ : QbarCell) from by decide +kernel) (show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_224))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_224) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_816_224) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(846,224,31)` of the square `4` of cusp `1`. -/
theorem ch_1_4_846_224 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_224))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 4 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 4 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 4 (slabL 1 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_4_846_224 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (846 : Fin 865)
      exact leaf_1_4_846
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (224 : Fin 865)
      exact leaf_1_4_224
    · show Work.RTOwed.kleinPt 4 (slabL 1 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (31 : Fin 865)
      exact leaf_1_4_31
  have hchart := cSimp_eq_chiRep 1 (a := 4) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_1_4_846_224 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_1_4_846_224) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (31 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_1_4_846_224)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_224) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨31⟩ : QbarCW.Cell) fl_1_4_846_224
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨846⟩ : QbarCell) < (⟨31⟩ : QbarCell) from lt_trans (show (⟨846⟩ : QbarCell) < (⟨224⟩ : QbarCell) from by decide +kernel) (show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨224⟩ : QbarCell) < (⟨31⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_224))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_224) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨141, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (31 : Fin 865)) fl_1_4_846_224) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(636,300,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_636_300 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_300))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_636_300 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (636 : Fin 865)
      exact leaf_1_5_636
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (300 : Fin 865)
      exact leaf_1_5_300
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_1_5_636_300 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_636_300) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_636_300)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_300) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_636_300
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨636⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨636⟩ : QbarCell) < (⟨300⟩ : QbarCell) from by decide +kernel) (show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_300))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_300) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_636_300) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(654,300,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_654_300 :
    cChain 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_300))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_654_300 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (654 : Fin 865)
      exact leaf_1_5_654
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (300 : Fin 865)
      exact leaf_1_5_300
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_1_5_654_300 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_654_300) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_654_300)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_300) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_654_300
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨654⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨654⟩ : QbarCell) < (⟨300⟩ : QbarCell) from by decide +kernel) (show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨300⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_300))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_300) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_654_300) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(594,304,52)` of the square `5` of cusp `1`. -/
theorem ch_1_5_594_304 :
    cChain 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 5 := by
    intro i
    intro j
    fin_cases i <;> fin_cases j <;>
      simp only [Work.RTOwed.cubeBox, Work.BridgeSquare.slabL, slabPt,
        Work.Cusp.lam2, Work.Cusp.lam3, Work.Cusp.kv, Work.Cusp.kappa,
        Work.Cusp.latMod, Work.RTOwed.cuspH, Work.BridgeSquare.cuspHm,
        Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa, Fin.isValue,
        Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hfar : ∀ j : Fin 3,
      (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 5 j : ℝ) + 1 := by
    intro j
    fin_cases j <;>
      simp only [Work.BridgeSquare.slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
        Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
        Work.BridgeSquare.cuspHm, Work.Cusp.cubeCorner, Work.BridgeSquare.dirKappa,
        Fin.isValue, Fin.reduceFinMk, ↓reduceIte, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, PiLp.neg_apply,
        WithLp.ofLp_smul, WithLp.ofLp_neg, WithLp.ofLp_sub] <;>
      norm_num
  have hpos : ∀ i : Fin 3,
      Work.RTOwed.kleinPt 5 (slabL 1 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_1_5_594_304 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (594 : Fin 865)
      exact leaf_1_5_594
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (304 : Fin 865)
      exact leaf_1_5_304
    · show Work.RTOwed.kleinPt 5 (slabL 1 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (52 : Fin 865)
      exact leaf_1_5_52
  have hchart := cSimp_eq_chiRep 1 (a := 5) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_1_5_594_304 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 1 (slabV 1 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_1_5_594_304) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (52 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_1_5_594_304)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨52⟩ : QbarCW.Cell) fl_1_5_594_304
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨594⟩ : QbarCell) < (⟨52⟩ : QbarCell) from lt_trans (show (⟨594⟩ : QbarCell) < (⟨304⟩ : QbarCell) from by decide +kernel) (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨304⟩ : QbarCell) < (⟨52⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨11, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (52 : Fin 865)) fl_1_5_594_304) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
