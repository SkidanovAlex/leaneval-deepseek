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

/-- The flag `(845 < 202 < 84)` of `Q̄`. -/
def fl_4_33_845_202 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨845⟩ : QbarCell)) (⟨202⟩ : QbarCell)
      (fun _ => show (⟨845⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide +kernel) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(839 < 322 < 84)` of `Q̄`. -/
def fl_4_33_839_322 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨839⟩ : QbarCell)) (⟨322⟩ : QbarCell)
      (fun _ => show (⟨839⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide +kernel) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(848 < 322 < 84)` of `Q̄`. -/
def fl_4_33_848_322 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨848⟩ : QbarCell)) (⟨322⟩ : QbarCell)
      (fun _ => show (⟨848⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide +kernel) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(705 < 423 < 84)` of `Q̄`. -/
def fl_4_33_705_423 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨705⟩ : QbarCell)) (⟨423⟩ : QbarCell)
      (fun _ => show (⟨705⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide +kernel) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(845 < 423 < 84)` of `Q̄`. -/
def fl_4_33_845_423 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨845⟩ : QbarCell)) (⟨423⟩ : QbarCell)
      (fun _ => show (⟨845⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide +kernel) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(705 < 431 < 84)` of `Q̄`. -/
def fl_4_33_705_431 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨705⟩ : QbarCell)) (⟨431⟩ : QbarCell)
      (fun _ => show (⟨705⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide +kernel) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(848 < 431 < 84)` of `Q̄`. -/
def fl_4_33_848_431 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨848⟩ : QbarCell)) (⟨431⟩ : QbarCell)
      (fun _ => show (⟨848⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide +kernel))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide +kernel) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide +kernel)

/-- The flag `(774 < 267 < 92)` of `Q̄`. -/
def fl_4_34_774_267 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨774⟩ : QbarCell)) (⟨267⟩ : QbarCell)
      (fun _ => show (⟨774⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide +kernel) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(797 < 267 < 92)` of `Q̄`. -/
def fl_4_34_797_267 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨797⟩ : QbarCell)) (⟨267⟩ : QbarCell)
      (fun _ => show (⟨797⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide +kernel) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(774 < 327 < 92)` of `Q̄`. -/
def fl_4_34_774_327 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨774⟩ : QbarCell)) (⟨327⟩ : QbarCell)
      (fun _ => show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(800 < 327 < 92)` of `Q̄`. -/
def fl_4_34_800_327 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨800⟩ : QbarCell)) (⟨327⟩ : QbarCell)
      (fun _ => show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide +kernel) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(648 < 435 < 92)` of `Q̄`. -/
def fl_4_34_648_435 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨648⟩ : QbarCell)) (⟨435⟩ : QbarCell)
      (fun _ => show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(797 < 435 < 92)` of `Q̄`. -/
def fl_4_34_797_435 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨797⟩ : QbarCell)) (⟨435⟩ : QbarCell)
      (fun _ => show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide +kernel) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(648 < 443 < 92)` of `Q̄`. -/
def fl_4_34_648_443 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨648⟩ : QbarCell)) (⟨443⟩ : QbarCell)
      (fun _ => show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(800 < 443 < 92)` of `Q̄`. -/
def fl_4_34_800_443 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨800⟩ : QbarCell)) (⟨443⟩ : QbarCell)
      (fun _ => show (⟨800⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide +kernel) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide +kernel)

/-- The flag `(807 < 207 < 99)` of `Q̄`. -/
def fl_4_37_807_207 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨807⟩ : QbarCell)) (⟨207⟩ : QbarCell)
      (fun _ => show (⟨807⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide +kernel) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(830 < 207 < 99)` of `Q̄`. -/
def fl_4_37_830_207 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨830⟩ : QbarCell)) (⟨207⟩ : QbarCell)
      (fun _ => show (⟨830⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide +kernel) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(807 < 371 < 99)` of `Q̄`. -/
def fl_4_37_807_371 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨807⟩ : QbarCell)) (⟨371⟩ : QbarCell)
      (fun _ => show (⟨807⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide +kernel) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(833 < 371 < 99)` of `Q̄`. -/
def fl_4_37_833_371 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨833⟩ : QbarCell)) (⟨371⟩ : QbarCell)
      (fun _ => show (⟨833⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide +kernel) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(687 < 451 < 99)` of `Q̄`. -/
def fl_4_37_687_451 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨687⟩ : QbarCell)) (⟨451⟩ : QbarCell)
      (fun _ => show (⟨687⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide +kernel) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(830 < 451 < 99)` of `Q̄`. -/
def fl_4_37_830_451 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨830⟩ : QbarCell)) (⟨451⟩ : QbarCell)
      (fun _ => show (⟨830⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide +kernel) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(687 < 459 < 99)` of `Q̄`. -/
def fl_4_37_687_459 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨687⟩ : QbarCell)) (⟨459⟩ : QbarCell)
      (fun _ => show (⟨687⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide +kernel) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(833 < 459 < 99)` of `Q̄`. -/
def fl_4_37_833_459 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨833⟩ : QbarCell)) (⟨459⟩ : QbarCell)
      (fun _ => show (⟨833⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide +kernel))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide +kernel) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide +kernel)

/-- The flag `(702 < 235 < 83)` of `Q̄`. -/
def fl_4_40_702_235 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨702⟩ : QbarCell)) (⟨235⟩ : QbarCell)
      (fun _ => show (⟨702⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide +kernel) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(725 < 235 < 83)` of `Q̄`. -/
def fl_4_40_725_235 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨725⟩ : QbarCell)) (⟨235⟩ : QbarCell)
      (fun _ => show (⟨725⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide +kernel) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(702 < 347 < 83)` of `Q̄`. -/
def fl_4_40_702_347 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨702⟩ : QbarCell)) (⟨347⟩ : QbarCell)
      (fun _ => show (⟨702⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide +kernel) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(728 < 347 < 83)` of `Q̄`. -/
def fl_4_40_728_347 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨728⟩ : QbarCell)) (⟨347⟩ : QbarCell)
      (fun _ => show (⟨728⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide +kernel) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(719 < 418 < 83)` of `Q̄`. -/
def fl_4_40_719_418 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨719⟩ : QbarCell)) (⟨418⟩ : QbarCell)
      (fun _ => show (⟨719⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide +kernel) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(725 < 418 < 83)` of `Q̄`. -/
def fl_4_40_725_418 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨725⟩ : QbarCell)) (⟨418⟩ : QbarCell)
      (fun _ => show (⟨725⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide +kernel) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(719 < 426 < 83)` of `Q̄`. -/
def fl_4_40_719_426 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨719⟩ : QbarCell)) (⟨426⟩ : QbarCell)
      (fun _ => show (⟨719⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide +kernel) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(728 < 426 < 83)` of `Q̄`. -/
def fl_4_40_728_426 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨728⟩ : QbarCell)) (⟨426⟩ : QbarCell)
      (fun _ => show (⟨728⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide +kernel))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide +kernel) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide +kernel)

/-- The flag `(840 < 203 < 85)` of `Q̄`. -/
def fl_4_44_840_203 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨840⟩ : QbarCell)) (⟨203⟩ : QbarCell)
      (fun _ => show (⟨840⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide +kernel) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(857 < 203 < 85)` of `Q̄`. -/
def fl_4_44_857_203 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨857⟩ : QbarCell)) (⟨203⟩ : QbarCell)
      (fun _ => show (⟨857⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide +kernel) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(840 < 323 < 85)` of `Q̄`. -/
def fl_4_44_840_323 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨840⟩ : QbarCell)) (⟨323⟩ : QbarCell)
      (fun _ => show (⟨840⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide +kernel) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(860 < 323 < 85)` of `Q̄`. -/
def fl_4_44_860_323 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨860⟩ : QbarCell)) (⟨323⟩ : QbarCell)
      (fun _ => show (⟨860⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide +kernel) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(720 < 419 < 85)` of `Q̄`. -/
def fl_4_44_720_419 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨720⟩ : QbarCell)) (⟨419⟩ : QbarCell)
      (fun _ => show (⟨720⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide +kernel) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(857 < 419 < 85)` of `Q̄`. -/
def fl_4_44_857_419 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨857⟩ : QbarCell)) (⟨419⟩ : QbarCell)
      (fun _ => show (⟨857⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide +kernel) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(720 < 427 < 85)` of `Q̄`. -/
def fl_4_44_720_427 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨720⟩ : QbarCell)) (⟨427⟩ : QbarCell)
      (fun _ => show (⟨720⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide +kernel) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-- The flag `(860 < 427 < 85)` of `Q̄`. -/
def fl_4_44_860_427 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨860⟩ : QbarCell)) (⟨427⟩ : QbarCell)
      (fun _ => show (⟨860⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide +kernel))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide +kernel) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide +kernel)

/-! ## The leaf points of the wall squares -/

/-- Leaf `103` of the square `16` of cusp `4`. -/
theorem leaf_4_16_103 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (103 : Fin 865) := by
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

/-- Leaf `302` of the square `16` of cusp `4`. -/
theorem leaf_4_16_302 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (302 : Fin 865) := by
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

/-- Leaf `398` of the square `16` of cusp `4`. -/
theorem leaf_4_16_398 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (398 : Fin 865) := by
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
