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

/-- The flag `(630 < 439 < 91)` of `Q̄`. -/
def fl_4_22_630_439 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨630⟩ : QbarCell)) (⟨439⟩ : QbarCell)
      (fun _ => show (⟨630⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨630⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨630⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide +kernel) (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(782 < 439 < 91)` of `Q̄`. -/
def fl_4_22_782_439 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨782⟩ : QbarCell)) (⟨439⟩ : QbarCell)
      (fun _ => show (⟨782⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide +kernel) (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(630 < 447 < 91)` of `Q̄`. -/
def fl_4_22_630_447 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨630⟩ : QbarCell)) (⟨447⟩ : QbarCell)
      (fun _ => show (⟨630⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨630⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨630⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide +kernel) (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(785 < 447 < 91)` of `Q̄`. -/
def fl_4_22_785_447 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨785⟩ : QbarCell)) (⟨447⟩ : QbarCell)
      (fun _ => show (⟨785⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide +kernel) (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(806 < 206 < 98)` of `Q̄`. -/
def fl_4_24_806_206 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨806⟩ : QbarCell)) (⟨206⟩ : QbarCell)
      (fun _ => show (⟨806⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨806⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨806⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide +kernel) (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(815 < 206 < 98)` of `Q̄`. -/
def fl_4_24_815_206 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨815⟩ : QbarCell)) (⟨206⟩ : QbarCell)
      (fun _ => show (⟨815⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨815⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨815⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide +kernel) (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(806 < 370 < 98)` of `Q̄`. -/
def fl_4_24_806_370 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨806⟩ : QbarCell)) (⟨370⟩ : QbarCell)
      (fun _ => show (⟨806⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨806⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨806⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide +kernel) (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(818 < 370 < 98)` of `Q̄`. -/
def fl_4_24_818_370 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨818⟩ : QbarCell)) (⟨370⟩ : QbarCell)
      (fun _ => show (⟨818⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide +kernel) (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(669 < 455 < 98)` of `Q̄`. -/
def fl_4_24_669_455 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨669⟩ : QbarCell)) (⟨455⟩ : QbarCell)
      (fun _ => show (⟨669⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide +kernel) (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(815 < 455 < 98)` of `Q̄`. -/
def fl_4_24_815_455 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨815⟩ : QbarCell)) (⟨455⟩ : QbarCell)
      (fun _ => show (⟨815⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨815⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨815⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide +kernel) (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(669 < 463 < 98)` of `Q̄`. -/
def fl_4_24_669_463 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨669⟩ : QbarCell)) (⟨463⟩ : QbarCell)
      (fun _ => show (⟨669⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide +kernel) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(818 < 463 < 98)` of `Q̄`. -/
def fl_4_24_818_463 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨818⟩ : QbarCell)) (⟨463⟩ : QbarCell)
      (fun _ => show (⟨818⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide +kernel))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide +kernel) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide +kernel)

/-- The flag `(735 < 271 < 106)` of `Q̄`. -/
def fl_4_25_735_271 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨735⟩ : QbarCell)) (⟨271⟩ : QbarCell)
      (fun _ => show (⟨735⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide +kernel) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(764 < 271 < 106)` of `Q̄`. -/
def fl_4_25_764_271 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨764⟩ : QbarCell)) (⟨271⟩ : QbarCell)
      (fun _ => show (⟨764⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide +kernel) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(735 < 375 < 106)` of `Q̄`. -/
def fl_4_25_735_375 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨735⟩ : QbarCell)) (⟨375⟩ : QbarCell)
      (fun _ => show (⟨735⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide +kernel) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(767 < 375 < 106)` of `Q̄`. -/
def fl_4_25_767_375 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨767⟩ : QbarCell)) (⟨375⟩ : QbarCell)
      (fun _ => show (⟨767⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨767⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨767⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide +kernel) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(609 < 467 < 106)` of `Q̄`. -/
def fl_4_25_609_467 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨609⟩ : QbarCell)) (⟨467⟩ : QbarCell)
      (fun _ => show (⟨609⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨609⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨609⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide +kernel) (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(764 < 467 < 106)` of `Q̄`. -/
def fl_4_25_764_467 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨764⟩ : QbarCell)) (⟨467⟩ : QbarCell)
      (fun _ => show (⟨764⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide +kernel) (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(609 < 475 < 106)` of `Q̄`. -/
def fl_4_25_609_475 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨609⟩ : QbarCell)) (⟨475⟩ : QbarCell)
      (fun _ => show (⟨609⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨609⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨609⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide +kernel) (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(767 < 475 < 106)` of `Q̄`. -/
def fl_4_25_767_475 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨767⟩ : QbarCell)) (⟨475⟩ : QbarCell)
      (fun _ => show (⟨767⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide +kernel))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨767⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨767⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide +kernel) (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide +kernel)

/-- The flag `(701 < 234 < 82)` of `Q̄`. -/
def fl_4_27_701_234 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨701⟩ : QbarCell)) (⟨234⟩ : QbarCell)
      (fun _ => show (⟨701⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide +kernel) (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(710 < 234 < 82)` of `Q̄`. -/
def fl_4_27_710_234 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨710⟩ : QbarCell)) (⟨234⟩ : QbarCell)
      (fun _ => show (⟨710⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide +kernel) (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(701 < 346 < 82)` of `Q̄`. -/
def fl_4_27_701_346 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨701⟩ : QbarCell)) (⟨346⟩ : QbarCell)
      (fun _ => show (⟨701⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide +kernel) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(713 < 346 < 82)` of `Q̄`. -/
def fl_4_27_713_346 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨713⟩ : QbarCell)) (⟨346⟩ : QbarCell)
      (fun _ => show (⟨713⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide +kernel) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(704 < 422 < 82)` of `Q̄`. -/
def fl_4_27_704_422 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨704⟩ : QbarCell)) (⟨422⟩ : QbarCell)
      (fun _ => show (⟨704⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide +kernel) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(710 < 422 < 82)` of `Q̄`. -/
def fl_4_27_710_422 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨710⟩ : QbarCell)) (⟨422⟩ : QbarCell)
      (fun _ => show (⟨710⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide +kernel) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(704 < 430 < 82)` of `Q̄`. -/
def fl_4_27_704_430 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨704⟩ : QbarCell)) (⟨430⟩ : QbarCell)
      (fun _ => show (⟨704⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide +kernel) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(713 < 430 < 82)` of `Q̄`. -/
def fl_4_27_713_430 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨713⟩ : QbarCell)) (⟨430⟩ : QbarCell)
      (fun _ => show (⟨713⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide +kernel))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide +kernel) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide +kernel)

/-- The flag `(624 < 299 < 90)` of `Q̄`. -/
def fl_4_28_624_299 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨624⟩ : QbarCell)) (⟨299⟩ : QbarCell)
      (fun _ => show (⟨624⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide +kernel) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(653 < 299 < 90)` of `Q̄`. -/
def fl_4_28_653_299 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨653⟩ : QbarCell)) (⟨299⟩ : QbarCell)
      (fun _ => show (⟨653⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide +kernel) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(624 < 351 < 90)` of `Q̄`. -/
def fl_4_28_624_351 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨624⟩ : QbarCell)) (⟨351⟩ : QbarCell)
      (fun _ => show (⟨624⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide +kernel) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(656 < 351 < 90)` of `Q̄`. -/
def fl_4_28_656_351 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨656⟩ : QbarCell)) (⟨351⟩ : QbarCell)
      (fun _ => show (⟨656⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide +kernel) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(647 < 434 < 90)` of `Q̄`. -/
def fl_4_28_647_434 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨647⟩ : QbarCell)) (⟨434⟩ : QbarCell)
      (fun _ => show (⟨647⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide +kernel) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(653 < 434 < 90)` of `Q̄`. -/
def fl_4_28_653_434 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨653⟩ : QbarCell)) (⟨434⟩ : QbarCell)
      (fun _ => show (⟨653⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide +kernel) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(647 < 442 < 90)` of `Q̄`. -/
def fl_4_28_647_442 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨647⟩ : QbarCell)) (⟨442⟩ : QbarCell)
      (fun _ => show (⟨647⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide +kernel) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(656 < 442 < 90)` of `Q̄`. -/
def fl_4_28_656_442 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨656⟩ : QbarCell)) (⟨442⟩ : QbarCell)
      (fun _ => show (⟨656⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide +kernel))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide +kernel) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide +kernel)

/-- The flag `(663 < 239 < 97)` of `Q̄`. -/
def fl_4_31_663_239 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨663⟩ : QbarCell)) (⟨239⟩ : QbarCell)
      (fun _ => show (⟨663⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide +kernel) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(692 < 239 < 97)` of `Q̄`. -/
def fl_4_31_692_239 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨692⟩ : QbarCell)) (⟨239⟩ : QbarCell)
      (fun _ => show (⟨692⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide +kernel) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(663 < 395 < 97)` of `Q̄`. -/
def fl_4_31_663_395 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨663⟩ : QbarCell)) (⟨395⟩ : QbarCell)
      (fun _ => show (⟨663⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide +kernel) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(695 < 395 < 97)` of `Q̄`. -/
def fl_4_31_695_395 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨695⟩ : QbarCell)) (⟨395⟩ : QbarCell)
      (fun _ => show (⟨695⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide +kernel) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(686 < 450 < 97)` of `Q̄`. -/
def fl_4_31_686_450 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨686⟩ : QbarCell)) (⟨450⟩ : QbarCell)
      (fun _ => show (⟨686⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide +kernel) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(692 < 450 < 97)` of `Q̄`. -/
def fl_4_31_692_450 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨692⟩ : QbarCell)) (⟨450⟩ : QbarCell)
      (fun _ => show (⟨692⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide +kernel) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(686 < 458 < 97)` of `Q̄`. -/
def fl_4_31_686_458 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨686⟩ : QbarCell)) (⟨458⟩ : QbarCell)
      (fun _ => show (⟨686⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide +kernel) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(695 < 458 < 97)` of `Q̄`. -/
def fl_4_31_695_458 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨695⟩ : QbarCell)) (⟨458⟩ : QbarCell)
      (fun _ => show (⟨695⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide +kernel))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide +kernel) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide +kernel)

/-- The flag `(839 < 202 < 84)` of `Q̄`. -/
def fl_4_33_839_202 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨839⟩ : QbarCell)) (⟨202⟩ : QbarCell)
      (fun _ => show (⟨839⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide +kernel) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)



end

end Work.BridgeSquare.SlabBuild
