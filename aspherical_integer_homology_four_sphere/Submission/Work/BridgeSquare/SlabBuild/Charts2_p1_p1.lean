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
      (fun _ => show (⟨801⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide +kernel) (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(861 < 340 < 170)` of `Q̄`. -/
def fl_2_8_861_340 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨861⟩ : QbarCell)) (⟨340⟩ : QbarCell)
      (fun _ => show (⟨861⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨340⟩ : QbarCell) from by decide +kernel) (show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨340⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(657 < 364 < 170)` of `Q̄`. -/
def fl_2_8_657_364 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨657⟩ : QbarCell)) (⟨364⟩ : QbarCell)
      (fun _ => show (⟨657⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide +kernel) (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(729 < 364 < 170)` of `Q̄`. -/
def fl_2_8_729_364 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨729⟩ : QbarCell)) (⟨364⟩ : QbarCell)
      (fun _ => show (⟨729⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨729⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨729⟩ : QbarCell) < (⟨364⟩ : QbarCell) from by decide +kernel) (show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨364⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(729 < 428 < 170)` of `Q̄`. -/
def fl_2_8_729_428 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨729⟩ : QbarCell)) (⟨428⟩ : QbarCell)
      (fun _ => show (⟨729⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨729⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨729⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide +kernel) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(861 < 428 < 170)` of `Q̄`. -/
def fl_2_8_861_428 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨861⟩ : QbarCell)) (⟨428⟩ : QbarCell)
      (fun _ => show (⟨861⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨861⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨861⟩ : QbarCell) < (⟨428⟩ : QbarCell) from by decide +kernel) (show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨428⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(657 < 444 < 170)` of `Q̄`. -/
def fl_2_8_657_444 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨657⟩ : QbarCell)) (⟨444⟩ : QbarCell)
      (fun _ => show (⟨657⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨657⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨657⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide +kernel) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(801 < 444 < 170)` of `Q̄`. -/
def fl_2_8_801_444 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨801⟩ : QbarCell)) (⟨444⟩ : QbarCell)
      (fun _ => show (⟨801⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide +kernel))
    (⟨170⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨801⟩ : QbarCell) < (⟨170⟩ : QbarCell) from lt_trans (show (⟨801⟩ : QbarCell) < (⟨444⟩ : QbarCell) from by decide +kernel) (show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨444⟩ : QbarCell) < (⟨170⟩ : QbarCell) from by decide +kernel)

/-- The flag `(768 < 388 < 177)` of `Q̄`. -/
def fl_2_9_768_388 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨768⟩ : QbarCell)) (⟨388⟩ : QbarCell)
      (fun _ => show (⟨768⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide +kernel) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(834 < 388 < 177)` of `Q̄`. -/
def fl_2_9_834_388 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨834⟩ : QbarCell)) (⟨388⟩ : QbarCell)
      (fun _ => show (⟨834⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨388⟩ : QbarCell) from by decide +kernel) (show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨388⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(618 < 412 < 177)` of `Q̄`. -/
def fl_2_9_618_412 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨618⟩ : QbarCell)) (⟨412⟩ : QbarCell)
      (fun _ => show (⟨618⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide +kernel) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(696 < 412 < 177)` of `Q̄`. -/
def fl_2_9_696_412 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨696⟩ : QbarCell)) (⟨412⟩ : QbarCell)
      (fun _ => show (⟨696⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨412⟩ : QbarCell) from by decide +kernel) (show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨412⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(696 < 460 < 177)` of `Q̄`. -/
def fl_2_9_696_460 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨696⟩ : QbarCell)) (⟨460⟩ : QbarCell)
      (fun _ => show (⟨696⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨696⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨696⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide +kernel) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(834 < 460 < 177)` of `Q̄`. -/
def fl_2_9_834_460 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨834⟩ : QbarCell)) (⟨460⟩ : QbarCell)
      (fun _ => show (⟨834⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨834⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨834⟩ : QbarCell) < (⟨460⟩ : QbarCell) from by decide +kernel) (show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨460⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(618 < 476 < 177)` of `Q̄`. -/
def fl_2_9_618_476 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨618⟩ : QbarCell)) (⟨476⟩ : QbarCell)
      (fun _ => show (⟨618⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨618⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨618⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide +kernel) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(768 < 476 < 177)` of `Q̄`. -/
def fl_2_9_768_476 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨768⟩ : QbarCell)) (⟨476⟩ : QbarCell)
      (fun _ => show (⟨768⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide +kernel))
    (⟨177⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨768⟩ : QbarCell) < (⟨177⟩ : QbarCell) from lt_trans (show (⟨768⟩ : QbarCell) < (⟨476⟩ : QbarCell) from by decide +kernel) (show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨476⟩ : QbarCell) < (⟨177⟩ : QbarCell) from by decide +kernel)

/-- The flag `(750 < 392 < 191)` of `Q̄`. -/
def fl_2_10_750_392 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨750⟩ : QbarCell)) (⟨392⟩ : QbarCell)
      (fun _ => show (⟨750⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide +kernel) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(819 < 392 < 191)` of `Q̄`. -/
def fl_2_10_819_392 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨819⟩ : QbarCell)) (⟨392⟩ : QbarCell)
      (fun _ => show (⟨819⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨392⟩ : QbarCell) from by decide +kernel) (show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨392⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(597 < 416 < 191)` of `Q̄`. -/
def fl_2_10_597_416 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨597⟩ : QbarCell)) (⟨416⟩ : QbarCell)
      (fun _ => show (⟨597⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide +kernel) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(678 < 416 < 191)` of `Q̄`. -/
def fl_2_10_678_416 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨678⟩ : QbarCell)) (⟨416⟩ : QbarCell)
      (fun _ => show (⟨678⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨416⟩ : QbarCell) from by decide +kernel) (show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨416⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(678 < 464 < 191)` of `Q̄`. -/
def fl_2_10_678_464 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨678⟩ : QbarCell)) (⟨464⟩ : QbarCell)
      (fun _ => show (⟨678⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨678⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨678⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide +kernel) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(819 < 464 < 191)` of `Q̄`. -/
def fl_2_10_819_464 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨819⟩ : QbarCell)) (⟨464⟩ : QbarCell)
      (fun _ => show (⟨819⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨819⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨819⟩ : QbarCell) < (⟨464⟩ : QbarCell) from by decide +kernel) (show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨464⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(597 < 480 < 191)` of `Q̄`. -/
def fl_2_10_597_480 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨597⟩ : QbarCell)) (⟨480⟩ : QbarCell)
      (fun _ => show (⟨597⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨597⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨597⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide +kernel) (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(750 < 480 < 191)` of `Q̄`. -/
def fl_2_10_750_480 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨750⟩ : QbarCell)) (⟨480⟩ : QbarCell)
      (fun _ => show (⟨750⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide +kernel))
    (⟨191⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨750⟩ : QbarCell) < (⟨191⟩ : QbarCell) from lt_trans (show (⟨750⟩ : QbarCell) < (⟨480⟩ : QbarCell) from by decide +kernel) (show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨480⟩ : QbarCell) < (⟨191⟩ : QbarCell) from by decide +kernel)

/-- The flag `(786 < 344 < 184)` of `Q̄`. -/
def fl_2_11_786_344 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨786⟩ : QbarCell)) (⟨344⟩ : QbarCell)
      (fun _ => show (⟨786⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨786⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨786⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide +kernel) (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(849 < 344 < 184)` of `Q̄`. -/
def fl_2_11_849_344 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨849⟩ : QbarCell)) (⟨344⟩ : QbarCell)
      (fun _ => show (⟨849⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨849⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨849⟩ : QbarCell) < (⟨344⟩ : QbarCell) from by decide +kernel) (show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨344⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(639 < 368 < 184)` of `Q̄`. -/
def fl_2_11_639_368 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨639⟩ : QbarCell)) (⟨368⟩ : QbarCell)
      (fun _ => show (⟨639⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨639⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨639⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide +kernel) (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(714 < 368 < 184)` of `Q̄`. -/
def fl_2_11_714_368 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨714⟩ : QbarCell)) (⟨368⟩ : QbarCell)
      (fun _ => show (⟨714⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨714⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨714⟩ : QbarCell) < (⟨368⟩ : QbarCell) from by decide +kernel) (show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨368⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(714 < 432 < 184)` of `Q̄`. -/
def fl_2_11_714_432 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨714⟩ : QbarCell)) (⟨432⟩ : QbarCell)
      (fun _ => show (⟨714⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨714⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨714⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide +kernel) (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(849 < 432 < 184)` of `Q̄`. -/
def fl_2_11_849_432 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨849⟩ : QbarCell)) (⟨432⟩ : QbarCell)
      (fun _ => show (⟨849⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨849⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨849⟩ : QbarCell) < (⟨432⟩ : QbarCell) from by decide +kernel) (show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨432⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(639 < 448 < 184)` of `Q̄`. -/
def fl_2_11_639_448 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨639⟩ : QbarCell)) (⟨448⟩ : QbarCell)
      (fun _ => show (⟨639⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨639⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨639⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide +kernel) (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

/-- The flag `(786 < 448 < 184)` of `Q̄`. -/
def fl_2_11_786_448 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨786⟩ : QbarCell)) (⟨448⟩ : QbarCell)
      (fun _ => show (⟨786⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide +kernel))
    (⟨184⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨786⟩ : QbarCell) < (⟨184⟩ : QbarCell) from lt_trans (show (⟨786⟩ : QbarCell) < (⟨448⟩ : QbarCell) from by decide +kernel) (show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨448⟩ : QbarCell) < (⟨184⟩ : QbarCell) from by decide +kernel)

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



end

end Work.BridgeSquare.SlabBuild
