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

/-- The flag `(801 < 340 < 170)` of `Q̄`. -/
def fl_2_8_801_340 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨801⟩ : QbarCell)) (⟨340⟩ : QbarCell)
      (fun _ => show (⟨801⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide) (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(861 < 340 < 170)` of `Q̄`. -/
def fl_2_8_861_340 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨861⟩ : QbarCell)) (⟨340⟩ : QbarCell)
      (fun _ => show (⟨861⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide) (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(657 < 364 < 170)` of `Q̄`. -/
def fl_2_8_657_364 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨657⟩ : QbarCell)) (⟨364⟩ : QbarCell)
      (fun _ => show (⟨657⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide) (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(729 < 364 < 170)` of `Q̄`. -/
def fl_2_8_729_364 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨729⟩ : QbarCell)) (⟨364⟩ : QbarCell)
      (fun _ => show (⟨729⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨729⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨729⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide) (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(729 < 428 < 170)` of `Q̄`. -/
def fl_2_8_729_428 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨729⟩ : QbarCell)) (⟨428⟩ : QbarCell)
      (fun _ => show (⟨729⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨729⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨729⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(861 < 428 < 170)` of `Q̄`. -/
def fl_2_8_861_428 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨861⟩ : QbarCell)) (⟨428⟩ : QbarCell)
      (fun _ => show (⟨861⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(657 < 444 < 170)` of `Q̄`. -/
def fl_2_8_657_444 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨657⟩ : QbarCell)) (⟨444⟩ : QbarCell)
      (fun _ => show (⟨657⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(801 < 444 < 170)` of `Q̄`. -/
def fl_2_8_801_444 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨801⟩ : QbarCell)) (⟨444⟩ : QbarCell)
      (fun _ => show (⟨801⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
      · exact show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)

/-- The flag `(768 < 388 < 177)` of `Q̄`. -/
def fl_2_9_768_388 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨768⟩ : QbarCell)) (⟨388⟩ : QbarCell)
      (fun _ => show (⟨768⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(834 < 388 < 177)` of `Q̄`. -/
def fl_2_9_834_388 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨834⟩ : QbarCell)) (⟨388⟩ : QbarCell)
      (fun _ => show (⟨834⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(618 < 412 < 177)` of `Q̄`. -/
def fl_2_9_618_412 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨618⟩ : QbarCell)) (⟨412⟩ : QbarCell)
      (fun _ => show (⟨618⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(696 < 412 < 177)` of `Q̄`. -/
def fl_2_9_696_412 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨696⟩ : QbarCell)) (⟨412⟩ : QbarCell)
      (fun _ => show (⟨696⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(696 < 460 < 177)` of `Q̄`. -/
def fl_2_9_696_460 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨696⟩ : QbarCell)) (⟨460⟩ : QbarCell)
      (fun _ => show (⟨696⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(834 < 460 < 177)` of `Q̄`. -/
def fl_2_9_834_460 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨834⟩ : QbarCell)) (⟨460⟩ : QbarCell)
      (fun _ => show (⟨834⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(618 < 476 < 177)` of `Q̄`. -/
def fl_2_9_618_476 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨618⟩ : QbarCell)) (⟨476⟩ : QbarCell)
      (fun _ => show (⟨618⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(768 < 476 < 177)` of `Q̄`. -/
def fl_2_9_768_476 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨768⟩ : QbarCell)) (⟨476⟩ : QbarCell)
      (fun _ => show (⟨768⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
      · exact show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)

/-- The flag `(750 < 392 < 191)` of `Q̄`. -/
def fl_2_10_750_392 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨750⟩ : QbarCell)) (⟨392⟩ : QbarCell)
      (fun _ => show (⟨750⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(819 < 392 < 191)` of `Q̄`. -/
def fl_2_10_819_392 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨819⟩ : QbarCell)) (⟨392⟩ : QbarCell)
      (fun _ => show (⟨819⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(597 < 416 < 191)` of `Q̄`. -/
def fl_2_10_597_416 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨597⟩ : QbarCell)) (⟨416⟩ : QbarCell)
      (fun _ => show (⟨597⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(678 < 416 < 191)` of `Q̄`. -/
def fl_2_10_678_416 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨678⟩ : QbarCell)) (⟨416⟩ : QbarCell)
      (fun _ => show (⟨678⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(678 < 464 < 191)` of `Q̄`. -/
def fl_2_10_678_464 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨678⟩ : QbarCell)) (⟨464⟩ : QbarCell)
      (fun _ => show (⟨678⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(819 < 464 < 191)` of `Q̄`. -/
def fl_2_10_819_464 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨819⟩ : QbarCell)) (⟨464⟩ : QbarCell)
      (fun _ => show (⟨819⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(597 < 480 < 191)` of `Q̄`. -/
def fl_2_10_597_480 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨597⟩ : QbarCell)) (⟨480⟩ : QbarCell)
      (fun _ => show (⟨597⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide) (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(750 < 480 < 191)` of `Q̄`. -/
def fl_2_10_750_480 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨750⟩ : QbarCell)) (⟨480⟩ : QbarCell)
      (fun _ => show (⟨750⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide) (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
      · exact show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)

/-- The flag `(786 < 344 < 184)` of `Q̄`. -/
def fl_2_11_786_344 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨786⟩ : QbarCell)) (⟨344⟩ : QbarCell)
      (fun _ => show (⟨786⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨786⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨786⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide) (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(849 < 344 < 184)` of `Q̄`. -/
def fl_2_11_849_344 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨849⟩ : QbarCell)) (⟨344⟩ : QbarCell)
      (fun _ => show (⟨849⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨849⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨849⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide) (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(639 < 368 < 184)` of `Q̄`. -/
def fl_2_11_639_368 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨639⟩ : QbarCell)) (⟨368⟩ : QbarCell)
      (fun _ => show (⟨639⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨639⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨639⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide) (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(714 < 368 < 184)` of `Q̄`. -/
def fl_2_11_714_368 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨714⟩ : QbarCell)) (⟨368⟩ : QbarCell)
      (fun _ => show (⟨714⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨714⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨714⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide) (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(714 < 432 < 184)` of `Q̄`. -/
def fl_2_11_714_432 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨714⟩ : QbarCell)) (⟨432⟩ : QbarCell)
      (fun _ => show (⟨714⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨714⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨714⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide) (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(849 < 432 < 184)` of `Q̄`. -/
def fl_2_11_849_432 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨849⟩ : QbarCell)) (⟨432⟩ : QbarCell)
      (fun _ => show (⟨849⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨849⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨849⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide) (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(639 < 448 < 184)` of `Q̄`. -/
def fl_2_11_639_448 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨639⟩ : QbarCell)) (⟨448⟩ : QbarCell)
      (fun _ => show (⟨639⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨639⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨639⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide) (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-- The flag `(786 < 448 < 184)` of `Q̄`. -/
def fl_2_11_786_448 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨786⟩ : QbarCell)) (⟨448⟩ : QbarCell)
      (fun _ => show (⟨786⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨786⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨786⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide) (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
      · exact show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)

/-! ## The leaf points of the wall squares -/

/-- Leaf `170` of the square `8` of cusp `2`. -/
theorem leaf_2_8_170 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (170 : Fin 865) := by
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

/-- Leaf `340` of the square `8` of cusp `2`. -/
theorem leaf_2_8_340 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (340 : Fin 865) := by
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

/-- Leaf `364` of the square `8` of cusp `2`. -/
theorem leaf_2_8_364 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (364 : Fin 865) := by
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

/-- Leaf `428` of the square `8` of cusp `2`. -/
theorem leaf_2_8_428 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (428 : Fin 865) := by
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

/-- Leaf `444` of the square `8` of cusp `2`. -/
theorem leaf_2_8_444 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (444 : Fin 865) := by
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

/-- Leaf `657` of the square `8` of cusp `2`. -/
theorem leaf_2_8_657 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (657 : Fin 865) := by
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

/-- Leaf `729` of the square `8` of cusp `2`. -/
theorem leaf_2_8_729 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (729 : Fin 865) := by
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

/-- Leaf `801` of the square `8` of cusp `2`. -/
theorem leaf_2_8_801 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (801 : Fin 865) := by
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

/-- Leaf `861` of the square `8` of cusp `2`. -/
theorem leaf_2_8_861 :
    Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (861 : Fin 865) := by
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

/-- Leaf `177` of the square `9` of cusp `2`. -/
theorem leaf_2_9_177 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (177 : Fin 865) := by
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

/-- Leaf `388` of the square `9` of cusp `2`. -/
theorem leaf_2_9_388 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (388 : Fin 865) := by
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

/-- Leaf `412` of the square `9` of cusp `2`. -/
theorem leaf_2_9_412 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (412 : Fin 865) := by
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

/-- Leaf `460` of the square `9` of cusp `2`. -/
theorem leaf_2_9_460 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (460 : Fin 865) := by
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

/-- Leaf `476` of the square `9` of cusp `2`. -/
theorem leaf_2_9_476 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (476 : Fin 865) := by
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

/-- Leaf `618` of the square `9` of cusp `2`. -/
theorem leaf_2_9_618 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (618 : Fin 865) := by
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

/-- Leaf `696` of the square `9` of cusp `2`. -/
theorem leaf_2_9_696 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (696 : Fin 865) := by
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

/-- Leaf `768` of the square `9` of cusp `2`. -/
theorem leaf_2_9_768 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (768 : Fin 865) := by
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

/-- Leaf `834` of the square `9` of cusp `2`. -/
theorem leaf_2_9_834 :
    Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (834 : Fin 865) := by
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

/-- Leaf `191` of the square `10` of cusp `2`. -/
theorem leaf_2_10_191 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (191 : Fin 865) := by
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

/-- Leaf `392` of the square `10` of cusp `2`. -/
theorem leaf_2_10_392 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (392 : Fin 865) := by
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

/-- Leaf `416` of the square `10` of cusp `2`. -/
theorem leaf_2_10_416 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (416 : Fin 865) := by
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

/-- Leaf `464` of the square `10` of cusp `2`. -/
theorem leaf_2_10_464 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (464 : Fin 865) := by
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

/-- Leaf `480` of the square `10` of cusp `2`. -/
theorem leaf_2_10_480 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (480 : Fin 865) := by
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

/-- Leaf `597` of the square `10` of cusp `2`. -/
theorem leaf_2_10_597 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (597 : Fin 865) := by
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

/-- Leaf `678` of the square `10` of cusp `2`. -/
theorem leaf_2_10_678 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (678 : Fin 865) := by
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

/-- Leaf `750` of the square `10` of cusp `2`. -/
theorem leaf_2_10_750 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (750 : Fin 865) := by
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

/-- Leaf `819` of the square `10` of cusp `2`. -/
theorem leaf_2_10_819 :
    Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (819 : Fin 865) := by
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

/-- Leaf `184` of the square `11` of cusp `2`. -/
theorem leaf_2_11_184 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (184 : Fin 865) := by
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

/-- Leaf `344` of the square `11` of cusp `2`. -/
theorem leaf_2_11_344 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (344 : Fin 865) := by
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

/-- Leaf `368` of the square `11` of cusp `2`. -/
theorem leaf_2_11_368 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (368 : Fin 865) := by
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

/-- Leaf `432` of the square `11` of cusp `2`. -/
theorem leaf_2_11_432 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (432 : Fin 865) := by
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

/-- Leaf `448` of the square `11` of cusp `2`. -/
theorem leaf_2_11_448 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (448 : Fin 865) := by
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

/-- Leaf `639` of the square `11` of cusp `2`. -/
theorem leaf_2_11_639 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (639 : Fin 865) := by
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

/-- Leaf `714` of the square `11` of cusp `2`. -/
theorem leaf_2_11_714 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (714 : Fin 865) := by
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

/-- Leaf `786` of the square `11` of cusp `2`. -/
theorem leaf_2_11_786 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (786 : Fin 865) := by
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

/-- Leaf `849` of the square `11` of cusp `2`. -/
theorem leaf_2_11_849 :
    Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (849 : Fin 865) := by
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

/-- The chart identity of the flag `(801,340,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_801_340 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_340))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_801_340 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (801 : Fin 865)
      exact leaf_2_8_801
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (340 : Fin 865)
      exact leaf_2_8_340
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_2_8_801_340 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_801_340) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_801_340)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_340) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_801_340
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide) (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_340))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_340) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_340) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(861,340,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_861_340 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_340))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_861_340 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (861 : Fin 865)
      exact leaf_2_8_861
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (340 : Fin 865)
      exact leaf_2_8_340
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_2_8_861_340 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_861_340) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_861_340)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_340) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_861_340
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide) (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_340))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_340) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_340) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(657,364,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_657_364 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_364))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_657_364 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (657 : Fin 865)
      exact leaf_2_8_657
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (364 : Fin 865)
      exact leaf_2_8_364
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_2_8_657_364 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_657_364) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_657_364)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_364) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_657_364
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide) (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_364))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_364) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_364) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(729,364,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_729_364 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_364))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_729_364 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (729 : Fin 865)
      exact leaf_2_8_729
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (364 : Fin 865)
      exact leaf_2_8_364
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_2_8_729_364 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_729_364) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_729_364)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_364) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_729_364
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨729⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨729⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide) (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_364))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_364) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_364) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(729,428,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_729_428 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_428))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_729_428 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (729 : Fin 865)
      exact leaf_2_8_729
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (428 : Fin 865)
      exact leaf_2_8_428
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_729_428 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_729_428) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_729_428)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_428) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_729_428
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨729⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨729⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_428))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_428) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_729_428) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(861,428,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_861_428 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_861_428 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (861 : Fin 865)
      exact leaf_2_8_861
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (428 : Fin 865)
      exact leaf_2_8_428
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_861_428 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_861_428) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_861_428)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_861_428
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_861_428) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(657,444,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_657_444 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_657_444 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (657 : Fin 865)
      exact leaf_2_8_657
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (444 : Fin 865)
      exact leaf_2_8_444
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_657_444 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_657_444) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_657_444)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_657_444
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_657_444) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(801,444,170)` of the square `8` of cusp `2`. -/
theorem ch_2_8_801_444 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 8 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 8 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 8 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_8_801_444 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (801 : Fin 865)
      exact leaf_2_8_801
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (444 : Fin 865)
      exact leaf_2_8_444
    · show Work.RTOwed.kleinPt 8 (slabL 2 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (170 : Fin 865)
      exact leaf_2_8_170
  have hchart := cSimp_eq_chiRep 2 (a := 8) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_2_8_801_444 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_8_801_444) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (170 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_8_801_444)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨170⟩ : QbarCW.Cell) fl_2_8_801_444
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨176, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (170 : Fin 865)) fl_2_8_801_444) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(768,388,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_768_388 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_768_388 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (768 : Fin 865)
      exact leaf_2_9_768
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (388 : Fin 865)
      exact leaf_2_9_388
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_768_388 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_768_388) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_768_388)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_768_388
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_388) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(834,388,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_834_388 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_834_388 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (834 : Fin 865)
      exact leaf_2_9_834
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (388 : Fin 865)
      exact leaf_2_9_388
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_834_388 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_834_388) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_834_388)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_834_388
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_388) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(618,412,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_618_412 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_412))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_618_412 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (618 : Fin 865)
      exact leaf_2_9_618
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (412 : Fin 865)
      exact leaf_2_9_412
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_618_412 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_618_412) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_618_412)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_412) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_618_412
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_412))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_412) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_412) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(696,412,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_696_412 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_696_412 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (696 : Fin 865)
      exact leaf_2_9_696
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (412 : Fin 865)
      exact leaf_2_9_412
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_2_9_696_412 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_696_412) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_696_412)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_696_412
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_412) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(696,460,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_696_460 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_696_460 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (696 : Fin 865)
      exact leaf_2_9_696
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (460 : Fin 865)
      exact leaf_2_9_460
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_696_460 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_696_460) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_696_460)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_696_460
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_696_460) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(834,460,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_834_460 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_834_460 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (834 : Fin 865)
      exact leaf_2_9_834
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (460 : Fin 865)
      exact leaf_2_9_460
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_834_460 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_834_460) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_834_460)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_834_460
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_834_460) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(618,476,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_618_476 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_618_476 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (618 : Fin 865)
      exact leaf_2_9_618
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (476 : Fin 865)
      exact leaf_2_9_476
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_618_476 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_618_476) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_618_476)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_618_476
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_618_476) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(768,476,177)` of the square `9` of cusp `2`. -/
theorem ch_2_9_768_476 :
    cChain 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 9 := by
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
      (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 9 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 9 (slabL 2 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_9_768_476 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (768 : Fin 865)
      exact leaf_2_9_768
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (476 : Fin 865)
      exact leaf_2_9_476
    · show Work.RTOwed.kleinPt 9 (slabL 2 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (177 : Fin 865)
      exact leaf_2_9_177
  have hchart := cSimp_eq_chiRep 2 (a := 9) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_2_9_768_476 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_2_9_768_476) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (177 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_2_9_768_476)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨177⟩ : QbarCW.Cell) fl_2_9_768_476
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨182, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (177 : Fin 865)) fl_2_9_768_476) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(750,392,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_750_392 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_750_392 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (750 : Fin 865)
      exact leaf_2_10_750
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (392 : Fin 865)
      exact leaf_2_10_392
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_750_392 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_750_392) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_750_392)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_750_392
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_392) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(819,392,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_819_392 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_819_392 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (819 : Fin 865)
      exact leaf_2_10_819
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (392 : Fin 865)
      exact leaf_2_10_392
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_819_392 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_819_392) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_819_392)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_819_392
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_392) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(597,416,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_597_416 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_597_416 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (597 : Fin 865)
      exact leaf_2_10_597
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (416 : Fin 865)
      exact leaf_2_10_416
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_597_416 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_597_416) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_597_416)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_597_416
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_416) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(678,416,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_678_416 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_678_416 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (678 : Fin 865)
      exact leaf_2_10_678
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (416 : Fin 865)
      exact leaf_2_10_416
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_2_10_678_416 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_678_416) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_678_416)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_678_416
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_416) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(678,464,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_678_464 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_678_464 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (678 : Fin 865)
      exact leaf_2_10_678
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (464 : Fin 865)
      exact leaf_2_10_464
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_2_10_678_464 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_678_464) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_678_464)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_678_464
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_678_464) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(819,464,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_819_464 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_464))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_819_464 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (819 : Fin 865)
      exact leaf_2_10_819
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (464 : Fin 865)
      exact leaf_2_10_464
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_2_10_819_464 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_819_464) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_819_464)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_464) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_819_464
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_464))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_464) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_819_464) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(597,480,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_597_480 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_480))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_597_480 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (597 : Fin 865)
      exact leaf_2_10_597
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (480 : Fin 865)
      exact leaf_2_10_480
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_2_10_597_480 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_597_480) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_597_480)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_480) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_597_480
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide) (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_480))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_480) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_597_480) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(750,480,191)` of the square `10` of cusp `2`. -/
theorem ch_2_10_750_480 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_480))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 10 := by
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
      (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 10 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 10 (slabL 2 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_10_750_480 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (750 : Fin 865)
      exact leaf_2_10_750
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (480 : Fin 865)
      exact leaf_2_10_480
    · show Work.RTOwed.kleinPt 10 (slabL 2 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (191 : Fin 865)
      exact leaf_2_10_191
  have hchart := cSimp_eq_chiRep 2 (a := 10) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_2_10_750_480 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_10_750_480) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (191 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_10_750_480)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_480) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨191⟩ : QbarCW.Cell) fl_2_10_750_480
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide) (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_480))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_480) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨94, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (191 : Fin 865)) fl_2_10_750_480) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(786,344,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_786_344 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_344))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_786_344 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (786 : Fin 865)
      exact leaf_2_11_786
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (344 : Fin 865)
      exact leaf_2_11_344
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_786_344 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_786_344) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_786_344)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_344) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_786_344
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨786⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨786⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide) (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_344))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_344) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_344) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(849,344,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_849_344 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_344))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_849_344 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (849 : Fin 865)
      exact leaf_2_11_849
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (344 : Fin 865)
      exact leaf_2_11_344
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_849_344 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_849_344) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_849_344)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_344) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_849_344
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨849⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨849⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide) (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_344))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_344) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_344) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(639,368,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_639_368 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_368))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_639_368 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (639 : Fin 865)
      exact leaf_2_11_639
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (368 : Fin 865)
      exact leaf_2_11_368
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_639_368 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_639_368) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_639_368)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_368) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_639_368
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨639⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨639⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide) (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_368))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_368) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_368) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(714,368,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_714_368 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_368))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_714_368 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (714 : Fin 865)
      exact leaf_2_11_714
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (368 : Fin 865)
      exact leaf_2_11_368
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_714_368 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_714_368) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_714_368)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_368) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_714_368
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨714⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨714⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide) (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_368))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_368) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_368) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(714,432,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_714_432 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_432))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_714_432 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (714 : Fin 865)
      exact leaf_2_11_714
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (432 : Fin 865)
      exact leaf_2_11_432
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_714_432 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_714_432) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_714_432)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_432) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_714_432
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨714⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨714⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide) (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_432))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_432) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_714_432) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(849,432,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_849_432 :
    cChain 2 (slabV 2 ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_432))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_849_432 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (849 : Fin 865)
      exact leaf_2_11_849
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (432 : Fin 865)
      exact leaf_2_11_432
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_849_432 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_849_432) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_849_432)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_432) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_849_432
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨849⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨849⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide) (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_432))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_432) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_849_432) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(639,448,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_639_448 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_448))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_639_448 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (639 : Fin 865)
      exact leaf_2_11_639
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (448 : Fin 865)
      exact leaf_2_11_448
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_639_448 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_639_448) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_639_448)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_448) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_639_448
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨639⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨639⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide) (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_448))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_448) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_639_448) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(786,448,184)` of the square `11` of cusp `2`. -/
theorem ch_2_11_786_448 :
    cChain 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_448))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 11 := by
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
      (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 11 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 11 (slabL 2 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_2_11_786_448 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (786 : Fin 865)
      exact leaf_2_11_786
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (448 : Fin 865)
      exact leaf_2_11_448
    · show Work.RTOwed.kleinPt 11 (slabL 2 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (184 : Fin 865)
      exact leaf_2_11_184
  have hchart := cSimp_eq_chiRep 2 (a := 11) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_2_11_786_448 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 2 (slabV 2 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_2_11_786_448) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (184 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_2_11_786_448)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_448) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨184⟩ : QbarCW.Cell) fl_2_11_786_448
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨786⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨786⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide) (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_448))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_448) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨88, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (184 : Fin 865)) fl_2_11_786_448) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
