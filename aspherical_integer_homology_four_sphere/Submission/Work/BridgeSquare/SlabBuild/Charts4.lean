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

/-- The flag `(578 < 302 < 103)` of `Q̄`. -/
def fl_4_16_578_302 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨578⟩ : QbarCell)) (⟨302⟩ : QbarCell)
      (fun _ => show (⟨578⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(593 < 302 < 103)` of `Q̄`. -/
def fl_4_16_593_302 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨593⟩ : QbarCell)) (⟨302⟩ : QbarCell)
      (fun _ => show (⟨593⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(578 < 398 < 103)` of `Q̄`. -/
def fl_4_16_578_398 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨578⟩ : QbarCell)) (⟨398⟩ : QbarCell)
      (fun _ => show (⟨578⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(596 < 398 < 103)` of `Q̄`. -/
def fl_4_16_596_398 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨596⟩ : QbarCell)) (⟨398⟩ : QbarCell)
      (fun _ => show (⟨596⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(587 < 470 < 103)` of `Q̄`. -/
def fl_4_16_587_470 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨587⟩ : QbarCell)) (⟨470⟩ : QbarCell)
      (fun _ => show (⟨587⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(593 < 470 < 103)` of `Q̄`. -/
def fl_4_16_593_470 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨593⟩ : QbarCell)) (⟨470⟩ : QbarCell)
      (fun _ => show (⟨593⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(587 < 478 < 103)` of `Q̄`. -/
def fl_4_16_587_478 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨587⟩ : QbarCell)) (⟨478⟩ : QbarCell)
      (fun _ => show (⟨587⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(596 < 478 < 103)` of `Q̄`. -/
def fl_4_16_596_478 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨596⟩ : QbarCell)) (⟨478⟩ : QbarCell)
      (fun _ => show (⟨596⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
      · exact show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)

/-- The flag `(734 < 270 < 105)` of `Q̄`. -/
def fl_4_17_734_270 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨734⟩ : QbarCell)) (⟨270⟩ : QbarCell)
      (fun _ => show (⟨734⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(746 < 270 < 105)` of `Q̄`. -/
def fl_4_17_746_270 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨746⟩ : QbarCell)) (⟨270⟩ : QbarCell)
      (fun _ => show (⟨746⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(734 < 374 < 105)` of `Q̄`. -/
def fl_4_17_734_374 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨734⟩ : QbarCell)) (⟨374⟩ : QbarCell)
      (fun _ => show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(749 < 374 < 105)` of `Q̄`. -/
def fl_4_17_749_374 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨749⟩ : QbarCell)) (⟨374⟩ : QbarCell)
      (fun _ => show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(588 < 471 < 105)` of `Q̄`. -/
def fl_4_17_588_471 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨588⟩ : QbarCell)) (⟨471⟩ : QbarCell)
      (fun _ => show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(746 < 471 < 105)` of `Q̄`. -/
def fl_4_17_746_471 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨746⟩ : QbarCell)) (⟨471⟩ : QbarCell)
      (fun _ => show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(588 < 479 < 105)` of `Q̄`. -/
def fl_4_17_588_479 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨588⟩ : QbarCell)) (⟨479⟩ : QbarCell)
      (fun _ => show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(749 < 479 < 105)` of `Q̄`. -/
def fl_4_17_749_479 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨749⟩ : QbarCell)) (⟨479⟩ : QbarCell)
      (fun _ => show (⟨749⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
      · exact show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)

/-- The flag `(623 < 298 < 89)` of `Q̄`. -/
def fl_4_18_623_298 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨623⟩ : QbarCell)) (⟨298⟩ : QbarCell)
      (fun _ => show (⟨623⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(635 < 298 < 89)` of `Q̄`. -/
def fl_4_18_635_298 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨635⟩ : QbarCell)) (⟨298⟩ : QbarCell)
      (fun _ => show (⟨635⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(623 < 350 < 89)` of `Q̄`. -/
def fl_4_18_623_350 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨623⟩ : QbarCell)) (⟨350⟩ : QbarCell)
      (fun _ => show (⟨623⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(638 < 350 < 89)` of `Q̄`. -/
def fl_4_18_638_350 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨638⟩ : QbarCell)) (⟨350⟩ : QbarCell)
      (fun _ => show (⟨638⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(629 < 438 < 89)` of `Q̄`. -/
def fl_4_18_629_438 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨629⟩ : QbarCell)) (⟨438⟩ : QbarCell)
      (fun _ => show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(635 < 438 < 89)` of `Q̄`. -/
def fl_4_18_635_438 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨635⟩ : QbarCell)) (⟨438⟩ : QbarCell)
      (fun _ => show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(629 < 446 < 89)` of `Q̄`. -/
def fl_4_18_629_446 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨629⟩ : QbarCell)) (⟨446⟩ : QbarCell)
      (fun _ => show (⟨629⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(638 < 446 < 89)` of `Q̄`. -/
def fl_4_18_638_446 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨638⟩ : QbarCell)) (⟨446⟩ : QbarCell)
      (fun _ => show (⟨638⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
      · exact show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)

/-- The flag `(662 < 238 < 96)` of `Q̄`. -/
def fl_4_20_662_238 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨662⟩ : QbarCell)) (⟨238⟩ : QbarCell)
      (fun _ => show (⟨662⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(674 < 238 < 96)` of `Q̄`. -/
def fl_4_20_674_238 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨674⟩ : QbarCell)) (⟨238⟩ : QbarCell)
      (fun _ => show (⟨674⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(662 < 394 < 96)` of `Q̄`. -/
def fl_4_20_662_394 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨662⟩ : QbarCell)) (⟨394⟩ : QbarCell)
      (fun _ => show (⟨662⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(677 < 394 < 96)` of `Q̄`. -/
def fl_4_20_677_394 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨677⟩ : QbarCell)) (⟨394⟩ : QbarCell)
      (fun _ => show (⟨677⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(668 < 454 < 96)` of `Q̄`. -/
def fl_4_20_668_454 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨668⟩ : QbarCell)) (⟨454⟩ : QbarCell)
      (fun _ => show (⟨668⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(674 < 454 < 96)` of `Q̄`. -/
def fl_4_20_674_454 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨674⟩ : QbarCell)) (⟨454⟩ : QbarCell)
      (fun _ => show (⟨674⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(668 < 462 < 96)` of `Q̄`. -/
def fl_4_20_668_462 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨668⟩ : QbarCell)) (⟨462⟩ : QbarCell)
      (fun _ => show (⟨668⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(677 < 462 < 96)` of `Q̄`. -/
def fl_4_20_677_462 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨677⟩ : QbarCell)) (⟨462⟩ : QbarCell)
      (fun _ => show (⟨677⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
      · exact show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)

/-- The flag `(579 < 303 < 104)` of `Q̄`. -/
def fl_4_21_579_303 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨579⟩ : QbarCell)) (⟨303⟩ : QbarCell)
      (fun _ => show (⟨579⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(614 < 303 < 104)` of `Q̄`. -/
def fl_4_21_614_303 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨614⟩ : QbarCell)) (⟨303⟩ : QbarCell)
      (fun _ => show (⟨614⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(579 < 399 < 104)` of `Q̄`. -/
def fl_4_21_579_399 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨579⟩ : QbarCell)) (⟨399⟩ : QbarCell)
      (fun _ => show (⟨579⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(617 < 399 < 104)` of `Q̄`. -/
def fl_4_21_617_399 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨617⟩ : QbarCell)) (⟨399⟩ : QbarCell)
      (fun _ => show (⟨617⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(608 < 466 < 104)` of `Q̄`. -/
def fl_4_21_608_466 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨608⟩ : QbarCell)) (⟨466⟩ : QbarCell)
      (fun _ => show (⟨608⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(614 < 466 < 104)` of `Q̄`. -/
def fl_4_21_614_466 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨614⟩ : QbarCell)) (⟨466⟩ : QbarCell)
      (fun _ => show (⟨614⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(608 < 474 < 104)` of `Q̄`. -/
def fl_4_21_608_474 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨608⟩ : QbarCell)) (⟨474⟩ : QbarCell)
      (fun _ => show (⟨608⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(617 < 474 < 104)` of `Q̄`. -/
def fl_4_21_617_474 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨617⟩ : QbarCell)) (⟨474⟩ : QbarCell)
      (fun _ => show (⟨617⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
      · exact show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)

/-- The flag `(773 < 266 < 91)` of `Q̄`. -/
def fl_4_22_773_266 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨773⟩ : QbarCell)) (⟨266⟩ : QbarCell)
      (fun _ => show (⟨773⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(782 < 266 < 91)` of `Q̄`. -/
def fl_4_22_782_266 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨782⟩ : QbarCell)) (⟨266⟩ : QbarCell)
      (fun _ => show (⟨782⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(773 < 326 < 91)` of `Q̄`. -/
def fl_4_22_773_326 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨773⟩ : QbarCell)) (⟨326⟩ : QbarCell)
      (fun _ => show (⟨773⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(785 < 326 < 91)` of `Q̄`. -/
def fl_4_22_785_326 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨785⟩ : QbarCell)) (⟨326⟩ : QbarCell)
      (fun _ => show (⟨785⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(630 < 439 < 91)` of `Q̄`. -/
def fl_4_22_630_439 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨630⟩ : QbarCell)) (⟨439⟩ : QbarCell)
      (fun _ => show (⟨630⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨630⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨630⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide) (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(782 < 439 < 91)` of `Q̄`. -/
def fl_4_22_782_439 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨782⟩ : QbarCell)) (⟨439⟩ : QbarCell)
      (fun _ => show (⟨782⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide) (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(630 < 447 < 91)` of `Q̄`. -/
def fl_4_22_630_447 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨630⟩ : QbarCell)) (⟨447⟩ : QbarCell)
      (fun _ => show (⟨630⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨630⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨630⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide) (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(785 < 447 < 91)` of `Q̄`. -/
def fl_4_22_785_447 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨785⟩ : QbarCell)) (⟨447⟩ : QbarCell)
      (fun _ => show (⟨785⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide) (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
      · exact show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)

/-- The flag `(806 < 206 < 98)` of `Q̄`. -/
def fl_4_24_806_206 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨806⟩ : QbarCell)) (⟨206⟩ : QbarCell)
      (fun _ => show (⟨806⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨806⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨806⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide) (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(815 < 206 < 98)` of `Q̄`. -/
def fl_4_24_815_206 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨815⟩ : QbarCell)) (⟨206⟩ : QbarCell)
      (fun _ => show (⟨815⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨815⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨815⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide) (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(806 < 370 < 98)` of `Q̄`. -/
def fl_4_24_806_370 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨806⟩ : QbarCell)) (⟨370⟩ : QbarCell)
      (fun _ => show (⟨806⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨806⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨806⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide) (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(818 < 370 < 98)` of `Q̄`. -/
def fl_4_24_818_370 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨818⟩ : QbarCell)) (⟨370⟩ : QbarCell)
      (fun _ => show (⟨818⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide) (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(669 < 455 < 98)` of `Q̄`. -/
def fl_4_24_669_455 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨669⟩ : QbarCell)) (⟨455⟩ : QbarCell)
      (fun _ => show (⟨669⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide) (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(815 < 455 < 98)` of `Q̄`. -/
def fl_4_24_815_455 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨815⟩ : QbarCell)) (⟨455⟩ : QbarCell)
      (fun _ => show (⟨815⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨815⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨815⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide) (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(669 < 463 < 98)` of `Q̄`. -/
def fl_4_24_669_463 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨669⟩ : QbarCell)) (⟨463⟩ : QbarCell)
      (fun _ => show (⟨669⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(818 < 463 < 98)` of `Q̄`. -/
def fl_4_24_818_463 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨818⟩ : QbarCell)) (⟨463⟩ : QbarCell)
      (fun _ => show (⟨818⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide))
    (⟨98⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
      · exact show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)

/-- The flag `(735 < 271 < 106)` of `Q̄`. -/
def fl_4_25_735_271 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨735⟩ : QbarCell)) (⟨271⟩ : QbarCell)
      (fun _ => show (⟨735⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(764 < 271 < 106)` of `Q̄`. -/
def fl_4_25_764_271 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨764⟩ : QbarCell)) (⟨271⟩ : QbarCell)
      (fun _ => show (⟨764⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(735 < 375 < 106)` of `Q̄`. -/
def fl_4_25_735_375 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨735⟩ : QbarCell)) (⟨375⟩ : QbarCell)
      (fun _ => show (⟨735⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(767 < 375 < 106)` of `Q̄`. -/
def fl_4_25_767_375 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨767⟩ : QbarCell)) (⟨375⟩ : QbarCell)
      (fun _ => show (⟨767⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨767⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨767⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(609 < 467 < 106)` of `Q̄`. -/
def fl_4_25_609_467 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨609⟩ : QbarCell)) (⟨467⟩ : QbarCell)
      (fun _ => show (⟨609⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨609⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨609⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide) (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(764 < 467 < 106)` of `Q̄`. -/
def fl_4_25_764_467 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨764⟩ : QbarCell)) (⟨467⟩ : QbarCell)
      (fun _ => show (⟨764⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide) (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(609 < 475 < 106)` of `Q̄`. -/
def fl_4_25_609_475 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨609⟩ : QbarCell)) (⟨475⟩ : QbarCell)
      (fun _ => show (⟨609⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨609⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨609⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide) (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(767 < 475 < 106)` of `Q̄`. -/
def fl_4_25_767_475 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨767⟩ : QbarCell)) (⟨475⟩ : QbarCell)
      (fun _ => show (⟨767⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide))
    (⟨106⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨767⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨767⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide) (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
      · exact show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)

/-- The flag `(701 < 234 < 82)` of `Q̄`. -/
def fl_4_27_701_234 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨701⟩ : QbarCell)) (⟨234⟩ : QbarCell)
      (fun _ => show (⟨701⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide) (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(710 < 234 < 82)` of `Q̄`. -/
def fl_4_27_710_234 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨710⟩ : QbarCell)) (⟨234⟩ : QbarCell)
      (fun _ => show (⟨710⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide) (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(701 < 346 < 82)` of `Q̄`. -/
def fl_4_27_701_346 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨701⟩ : QbarCell)) (⟨346⟩ : QbarCell)
      (fun _ => show (⟨701⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(713 < 346 < 82)` of `Q̄`. -/
def fl_4_27_713_346 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨713⟩ : QbarCell)) (⟨346⟩ : QbarCell)
      (fun _ => show (⟨713⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(704 < 422 < 82)` of `Q̄`. -/
def fl_4_27_704_422 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨704⟩ : QbarCell)) (⟨422⟩ : QbarCell)
      (fun _ => show (⟨704⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(710 < 422 < 82)` of `Q̄`. -/
def fl_4_27_710_422 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨710⟩ : QbarCell)) (⟨422⟩ : QbarCell)
      (fun _ => show (⟨710⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(704 < 430 < 82)` of `Q̄`. -/
def fl_4_27_704_430 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨704⟩ : QbarCell)) (⟨430⟩ : QbarCell)
      (fun _ => show (⟨704⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(713 < 430 < 82)` of `Q̄`. -/
def fl_4_27_713_430 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨713⟩ : QbarCell)) (⟨430⟩ : QbarCell)
      (fun _ => show (⟨713⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide))
    (⟨82⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
      · exact show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)

/-- The flag `(624 < 299 < 90)` of `Q̄`. -/
def fl_4_28_624_299 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨624⟩ : QbarCell)) (⟨299⟩ : QbarCell)
      (fun _ => show (⟨624⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(653 < 299 < 90)` of `Q̄`. -/
def fl_4_28_653_299 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨653⟩ : QbarCell)) (⟨299⟩ : QbarCell)
      (fun _ => show (⟨653⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(624 < 351 < 90)` of `Q̄`. -/
def fl_4_28_624_351 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨624⟩ : QbarCell)) (⟨351⟩ : QbarCell)
      (fun _ => show (⟨624⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(656 < 351 < 90)` of `Q̄`. -/
def fl_4_28_656_351 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨656⟩ : QbarCell)) (⟨351⟩ : QbarCell)
      (fun _ => show (⟨656⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(647 < 434 < 90)` of `Q̄`. -/
def fl_4_28_647_434 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨647⟩ : QbarCell)) (⟨434⟩ : QbarCell)
      (fun _ => show (⟨647⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(653 < 434 < 90)` of `Q̄`. -/
def fl_4_28_653_434 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨653⟩ : QbarCell)) (⟨434⟩ : QbarCell)
      (fun _ => show (⟨653⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(647 < 442 < 90)` of `Q̄`. -/
def fl_4_28_647_442 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨647⟩ : QbarCell)) (⟨442⟩ : QbarCell)
      (fun _ => show (⟨647⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(656 < 442 < 90)` of `Q̄`. -/
def fl_4_28_656_442 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨656⟩ : QbarCell)) (⟨442⟩ : QbarCell)
      (fun _ => show (⟨656⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide))
    (⟨90⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
      · exact show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)

/-- The flag `(663 < 239 < 97)` of `Q̄`. -/
def fl_4_31_663_239 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨663⟩ : QbarCell)) (⟨239⟩ : QbarCell)
      (fun _ => show (⟨663⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(692 < 239 < 97)` of `Q̄`. -/
def fl_4_31_692_239 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨692⟩ : QbarCell)) (⟨239⟩ : QbarCell)
      (fun _ => show (⟨692⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(663 < 395 < 97)` of `Q̄`. -/
def fl_4_31_663_395 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨663⟩ : QbarCell)) (⟨395⟩ : QbarCell)
      (fun _ => show (⟨663⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(695 < 395 < 97)` of `Q̄`. -/
def fl_4_31_695_395 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨695⟩ : QbarCell)) (⟨395⟩ : QbarCell)
      (fun _ => show (⟨695⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(686 < 450 < 97)` of `Q̄`. -/
def fl_4_31_686_450 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨686⟩ : QbarCell)) (⟨450⟩ : QbarCell)
      (fun _ => show (⟨686⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(692 < 450 < 97)` of `Q̄`. -/
def fl_4_31_692_450 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨692⟩ : QbarCell)) (⟨450⟩ : QbarCell)
      (fun _ => show (⟨692⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(686 < 458 < 97)` of `Q̄`. -/
def fl_4_31_686_458 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨686⟩ : QbarCell)) (⟨458⟩ : QbarCell)
      (fun _ => show (⟨686⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(695 < 458 < 97)` of `Q̄`. -/
def fl_4_31_695_458 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨695⟩ : QbarCell)) (⟨458⟩ : QbarCell)
      (fun _ => show (⟨695⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide))
    (⟨97⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
      · exact show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)

/-- The flag `(839 < 202 < 84)` of `Q̄`. -/
def fl_4_33_839_202 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨839⟩ : QbarCell)) (⟨202⟩ : QbarCell)
      (fun _ => show (⟨839⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(845 < 202 < 84)` of `Q̄`. -/
def fl_4_33_845_202 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨845⟩ : QbarCell)) (⟨202⟩ : QbarCell)
      (fun _ => show (⟨845⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(839 < 322 < 84)` of `Q̄`. -/
def fl_4_33_839_322 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨839⟩ : QbarCell)) (⟨322⟩ : QbarCell)
      (fun _ => show (⟨839⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(848 < 322 < 84)` of `Q̄`. -/
def fl_4_33_848_322 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨848⟩ : QbarCell)) (⟨322⟩ : QbarCell)
      (fun _ => show (⟨848⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(705 < 423 < 84)` of `Q̄`. -/
def fl_4_33_705_423 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨705⟩ : QbarCell)) (⟨423⟩ : QbarCell)
      (fun _ => show (⟨705⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(845 < 423 < 84)` of `Q̄`. -/
def fl_4_33_845_423 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨845⟩ : QbarCell)) (⟨423⟩ : QbarCell)
      (fun _ => show (⟨845⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(705 < 431 < 84)` of `Q̄`. -/
def fl_4_33_705_431 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨705⟩ : QbarCell)) (⟨431⟩ : QbarCell)
      (fun _ => show (⟨705⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(848 < 431 < 84)` of `Q̄`. -/
def fl_4_33_848_431 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨848⟩ : QbarCell)) (⟨431⟩ : QbarCell)
      (fun _ => show (⟨848⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide))
    (⟨84⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
      · exact show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)

/-- The flag `(774 < 267 < 92)` of `Q̄`. -/
def fl_4_34_774_267 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨774⟩ : QbarCell)) (⟨267⟩ : QbarCell)
      (fun _ => show (⟨774⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(797 < 267 < 92)` of `Q̄`. -/
def fl_4_34_797_267 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨797⟩ : QbarCell)) (⟨267⟩ : QbarCell)
      (fun _ => show (⟨797⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(774 < 327 < 92)` of `Q̄`. -/
def fl_4_34_774_327 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨774⟩ : QbarCell)) (⟨327⟩ : QbarCell)
      (fun _ => show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(800 < 327 < 92)` of `Q̄`. -/
def fl_4_34_800_327 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨800⟩ : QbarCell)) (⟨327⟩ : QbarCell)
      (fun _ => show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(648 < 435 < 92)` of `Q̄`. -/
def fl_4_34_648_435 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨648⟩ : QbarCell)) (⟨435⟩ : QbarCell)
      (fun _ => show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(797 < 435 < 92)` of `Q̄`. -/
def fl_4_34_797_435 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨797⟩ : QbarCell)) (⟨435⟩ : QbarCell)
      (fun _ => show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(648 < 443 < 92)` of `Q̄`. -/
def fl_4_34_648_443 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨648⟩ : QbarCell)) (⟨443⟩ : QbarCell)
      (fun _ => show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(800 < 443 < 92)` of `Q̄`. -/
def fl_4_34_800_443 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨800⟩ : QbarCell)) (⟨443⟩ : QbarCell)
      (fun _ => show (⟨800⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide))
    (⟨92⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
      · exact show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)

/-- The flag `(807 < 207 < 99)` of `Q̄`. -/
def fl_4_37_807_207 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨807⟩ : QbarCell)) (⟨207⟩ : QbarCell)
      (fun _ => show (⟨807⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(830 < 207 < 99)` of `Q̄`. -/
def fl_4_37_830_207 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨830⟩ : QbarCell)) (⟨207⟩ : QbarCell)
      (fun _ => show (⟨830⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(807 < 371 < 99)` of `Q̄`. -/
def fl_4_37_807_371 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨807⟩ : QbarCell)) (⟨371⟩ : QbarCell)
      (fun _ => show (⟨807⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(833 < 371 < 99)` of `Q̄`. -/
def fl_4_37_833_371 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨833⟩ : QbarCell)) (⟨371⟩ : QbarCell)
      (fun _ => show (⟨833⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(687 < 451 < 99)` of `Q̄`. -/
def fl_4_37_687_451 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨687⟩ : QbarCell)) (⟨451⟩ : QbarCell)
      (fun _ => show (⟨687⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(830 < 451 < 99)` of `Q̄`. -/
def fl_4_37_830_451 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨830⟩ : QbarCell)) (⟨451⟩ : QbarCell)
      (fun _ => show (⟨830⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(687 < 459 < 99)` of `Q̄`. -/
def fl_4_37_687_459 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨687⟩ : QbarCell)) (⟨459⟩ : QbarCell)
      (fun _ => show (⟨687⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(833 < 459 < 99)` of `Q̄`. -/
def fl_4_37_833_459 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨833⟩ : QbarCell)) (⟨459⟩ : QbarCell)
      (fun _ => show (⟨833⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide))
    (⟨99⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
      · exact show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)

/-- The flag `(702 < 235 < 83)` of `Q̄`. -/
def fl_4_40_702_235 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨702⟩ : QbarCell)) (⟨235⟩ : QbarCell)
      (fun _ => show (⟨702⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(725 < 235 < 83)` of `Q̄`. -/
def fl_4_40_725_235 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨725⟩ : QbarCell)) (⟨235⟩ : QbarCell)
      (fun _ => show (⟨725⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(702 < 347 < 83)` of `Q̄`. -/
def fl_4_40_702_347 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨702⟩ : QbarCell)) (⟨347⟩ : QbarCell)
      (fun _ => show (⟨702⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(728 < 347 < 83)` of `Q̄`. -/
def fl_4_40_728_347 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨728⟩ : QbarCell)) (⟨347⟩ : QbarCell)
      (fun _ => show (⟨728⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(719 < 418 < 83)` of `Q̄`. -/
def fl_4_40_719_418 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨719⟩ : QbarCell)) (⟨418⟩ : QbarCell)
      (fun _ => show (⟨719⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(725 < 418 < 83)` of `Q̄`. -/
def fl_4_40_725_418 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨725⟩ : QbarCell)) (⟨418⟩ : QbarCell)
      (fun _ => show (⟨725⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(719 < 426 < 83)` of `Q̄`. -/
def fl_4_40_719_426 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨719⟩ : QbarCell)) (⟨426⟩ : QbarCell)
      (fun _ => show (⟨719⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(728 < 426 < 83)` of `Q̄`. -/
def fl_4_40_728_426 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨728⟩ : QbarCell)) (⟨426⟩ : QbarCell)
      (fun _ => show (⟨728⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide))
    (⟨83⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
      · exact show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)

/-- The flag `(840 < 203 < 85)` of `Q̄`. -/
def fl_4_44_840_203 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨840⟩ : QbarCell)) (⟨203⟩ : QbarCell)
      (fun _ => show (⟨840⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(857 < 203 < 85)` of `Q̄`. -/
def fl_4_44_857_203 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨857⟩ : QbarCell)) (⟨203⟩ : QbarCell)
      (fun _ => show (⟨857⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(840 < 323 < 85)` of `Q̄`. -/
def fl_4_44_840_323 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨840⟩ : QbarCell)) (⟨323⟩ : QbarCell)
      (fun _ => show (⟨840⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(860 < 323 < 85)` of `Q̄`. -/
def fl_4_44_860_323 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨860⟩ : QbarCell)) (⟨323⟩ : QbarCell)
      (fun _ => show (⟨860⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(720 < 419 < 85)` of `Q̄`. -/
def fl_4_44_720_419 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨720⟩ : QbarCell)) (⟨419⟩ : QbarCell)
      (fun _ => show (⟨720⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(857 < 419 < 85)` of `Q̄`. -/
def fl_4_44_857_419 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨857⟩ : QbarCell)) (⟨419⟩ : QbarCell)
      (fun _ => show (⟨857⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(720 < 427 < 85)` of `Q̄`. -/
def fl_4_44_720_427 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨720⟩ : QbarCell)) (⟨427⟩ : QbarCell)
      (fun _ => show (⟨720⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

/-- The flag `(860 < 427 < 85)` of `Q̄`. -/
def fl_4_44_860_427 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨860⟩ : QbarCell)) (⟨427⟩ : QbarCell)
      (fun _ => show (⟨860⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide))
    (⟨85⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
      · exact show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)

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

/-- Leaf `470` of the square `16` of cusp `4`. -/
theorem leaf_4_16_470 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (470 : Fin 865) := by
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

/-- Leaf `478` of the square `16` of cusp `4`. -/
theorem leaf_4_16_478 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (478 : Fin 865) := by
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

/-- Leaf `578` of the square `16` of cusp `4`. -/
theorem leaf_4_16_578 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (578 : Fin 865) := by
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

/-- Leaf `587` of the square `16` of cusp `4`. -/
theorem leaf_4_16_587 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (587 : Fin 865) := by
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

/-- Leaf `593` of the square `16` of cusp `4`. -/
theorem leaf_4_16_593 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (593 : Fin 865) := by
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

/-- Leaf `596` of the square `16` of cusp `4`. -/
theorem leaf_4_16_596 :
    Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (596 : Fin 865) := by
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

/-- Leaf `105` of the square `17` of cusp `4`. -/
theorem leaf_4_17_105 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (105 : Fin 865) := by
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

/-- Leaf `270` of the square `17` of cusp `4`. -/
theorem leaf_4_17_270 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (270 : Fin 865) := by
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

/-- Leaf `374` of the square `17` of cusp `4`. -/
theorem leaf_4_17_374 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (374 : Fin 865) := by
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

/-- Leaf `471` of the square `17` of cusp `4`. -/
theorem leaf_4_17_471 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (471 : Fin 865) := by
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

/-- Leaf `479` of the square `17` of cusp `4`. -/
theorem leaf_4_17_479 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (479 : Fin 865) := by
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

/-- Leaf `588` of the square `17` of cusp `4`. -/
theorem leaf_4_17_588 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (588 : Fin 865) := by
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

/-- Leaf `734` of the square `17` of cusp `4`. -/
theorem leaf_4_17_734 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (734 : Fin 865) := by
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

/-- Leaf `746` of the square `17` of cusp `4`. -/
theorem leaf_4_17_746 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (746 : Fin 865) := by
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

/-- Leaf `749` of the square `17` of cusp `4`. -/
theorem leaf_4_17_749 :
    Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (749 : Fin 865) := by
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

/-- Leaf `89` of the square `18` of cusp `4`. -/
theorem leaf_4_18_89 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (89 : Fin 865) := by
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

/-- Leaf `298` of the square `18` of cusp `4`. -/
theorem leaf_4_18_298 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (298 : Fin 865) := by
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

/-- Leaf `350` of the square `18` of cusp `4`. -/
theorem leaf_4_18_350 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (350 : Fin 865) := by
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

/-- Leaf `438` of the square `18` of cusp `4`. -/
theorem leaf_4_18_438 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (438 : Fin 865) := by
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

/-- Leaf `446` of the square `18` of cusp `4`. -/
theorem leaf_4_18_446 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (446 : Fin 865) := by
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

/-- Leaf `623` of the square `18` of cusp `4`. -/
theorem leaf_4_18_623 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (623 : Fin 865) := by
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

/-- Leaf `629` of the square `18` of cusp `4`. -/
theorem leaf_4_18_629 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (629 : Fin 865) := by
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

/-- Leaf `635` of the square `18` of cusp `4`. -/
theorem leaf_4_18_635 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (635 : Fin 865) := by
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

/-- Leaf `638` of the square `18` of cusp `4`. -/
theorem leaf_4_18_638 :
    Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (638 : Fin 865) := by
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

/-- Leaf `96` of the square `20` of cusp `4`. -/
theorem leaf_4_20_96 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (96 : Fin 865) := by
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

/-- Leaf `238` of the square `20` of cusp `4`. -/
theorem leaf_4_20_238 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (238 : Fin 865) := by
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

/-- Leaf `394` of the square `20` of cusp `4`. -/
theorem leaf_4_20_394 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (394 : Fin 865) := by
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

/-- Leaf `454` of the square `20` of cusp `4`. -/
theorem leaf_4_20_454 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (454 : Fin 865) := by
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

/-- Leaf `462` of the square `20` of cusp `4`. -/
theorem leaf_4_20_462 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (462 : Fin 865) := by
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

/-- Leaf `662` of the square `20` of cusp `4`. -/
theorem leaf_4_20_662 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (662 : Fin 865) := by
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

/-- Leaf `668` of the square `20` of cusp `4`. -/
theorem leaf_4_20_668 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (668 : Fin 865) := by
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

/-- Leaf `674` of the square `20` of cusp `4`. -/
theorem leaf_4_20_674 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (674 : Fin 865) := by
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

/-- Leaf `677` of the square `20` of cusp `4`. -/
theorem leaf_4_20_677 :
    Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (677 : Fin 865) := by
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

/-- Leaf `104` of the square `21` of cusp `4`. -/
theorem leaf_4_21_104 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (104 : Fin 865) := by
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

/-- Leaf `303` of the square `21` of cusp `4`. -/
theorem leaf_4_21_303 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (303 : Fin 865) := by
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

/-- Leaf `399` of the square `21` of cusp `4`. -/
theorem leaf_4_21_399 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (399 : Fin 865) := by
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

/-- Leaf `466` of the square `21` of cusp `4`. -/
theorem leaf_4_21_466 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (466 : Fin 865) := by
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

/-- Leaf `474` of the square `21` of cusp `4`. -/
theorem leaf_4_21_474 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (474 : Fin 865) := by
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

/-- Leaf `579` of the square `21` of cusp `4`. -/
theorem leaf_4_21_579 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (579 : Fin 865) := by
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

/-- Leaf `608` of the square `21` of cusp `4`. -/
theorem leaf_4_21_608 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (608 : Fin 865) := by
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

/-- Leaf `614` of the square `21` of cusp `4`. -/
theorem leaf_4_21_614 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (614 : Fin 865) := by
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

/-- Leaf `617` of the square `21` of cusp `4`. -/
theorem leaf_4_21_617 :
    Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (617 : Fin 865) := by
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

/-- Leaf `91` of the square `22` of cusp `4`. -/
theorem leaf_4_22_91 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (91 : Fin 865) := by
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

/-- Leaf `266` of the square `22` of cusp `4`. -/
theorem leaf_4_22_266 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (266 : Fin 865) := by
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

/-- Leaf `326` of the square `22` of cusp `4`. -/
theorem leaf_4_22_326 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (326 : Fin 865) := by
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

/-- Leaf `439` of the square `22` of cusp `4`. -/
theorem leaf_4_22_439 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (439 : Fin 865) := by
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

/-- Leaf `447` of the square `22` of cusp `4`. -/
theorem leaf_4_22_447 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (447 : Fin 865) := by
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

/-- Leaf `630` of the square `22` of cusp `4`. -/
theorem leaf_4_22_630 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (630 : Fin 865) := by
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

/-- Leaf `773` of the square `22` of cusp `4`. -/
theorem leaf_4_22_773 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (773 : Fin 865) := by
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

/-- Leaf `782` of the square `22` of cusp `4`. -/
theorem leaf_4_22_782 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (782 : Fin 865) := by
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

/-- Leaf `785` of the square `22` of cusp `4`. -/
theorem leaf_4_22_785 :
    Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (785 : Fin 865) := by
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

/-- Leaf `98` of the square `24` of cusp `4`. -/
theorem leaf_4_24_98 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (98 : Fin 865) := by
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

/-- Leaf `206` of the square `24` of cusp `4`. -/
theorem leaf_4_24_206 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (206 : Fin 865) := by
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

/-- Leaf `370` of the square `24` of cusp `4`. -/
theorem leaf_4_24_370 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (370 : Fin 865) := by
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

/-- Leaf `455` of the square `24` of cusp `4`. -/
theorem leaf_4_24_455 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (455 : Fin 865) := by
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

/-- Leaf `463` of the square `24` of cusp `4`. -/
theorem leaf_4_24_463 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (463 : Fin 865) := by
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

/-- Leaf `669` of the square `24` of cusp `4`. -/
theorem leaf_4_24_669 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (669 : Fin 865) := by
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

/-- Leaf `806` of the square `24` of cusp `4`. -/
theorem leaf_4_24_806 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (806 : Fin 865) := by
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

/-- Leaf `815` of the square `24` of cusp `4`. -/
theorem leaf_4_24_815 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (815 : Fin 865) := by
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

/-- Leaf `818` of the square `24` of cusp `4`. -/
theorem leaf_4_24_818 :
    Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (818 : Fin 865) := by
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

/-- Leaf `106` of the square `25` of cusp `4`. -/
theorem leaf_4_25_106 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (106 : Fin 865) := by
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

/-- Leaf `271` of the square `25` of cusp `4`. -/
theorem leaf_4_25_271 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (271 : Fin 865) := by
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

/-- Leaf `375` of the square `25` of cusp `4`. -/
theorem leaf_4_25_375 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (375 : Fin 865) := by
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

/-- Leaf `467` of the square `25` of cusp `4`. -/
theorem leaf_4_25_467 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (467 : Fin 865) := by
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

/-- Leaf `475` of the square `25` of cusp `4`. -/
theorem leaf_4_25_475 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (475 : Fin 865) := by
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

/-- Leaf `609` of the square `25` of cusp `4`. -/
theorem leaf_4_25_609 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (609 : Fin 865) := by
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

/-- Leaf `735` of the square `25` of cusp `4`. -/
theorem leaf_4_25_735 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (735 : Fin 865) := by
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

/-- Leaf `764` of the square `25` of cusp `4`. -/
theorem leaf_4_25_764 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (764 : Fin 865) := by
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

/-- Leaf `767` of the square `25` of cusp `4`. -/
theorem leaf_4_25_767 :
    Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (767 : Fin 865) := by
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

/-- Leaf `82` of the square `27` of cusp `4`. -/
theorem leaf_4_27_82 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (82 : Fin 865) := by
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

/-- Leaf `234` of the square `27` of cusp `4`. -/
theorem leaf_4_27_234 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (234 : Fin 865) := by
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

/-- Leaf `346` of the square `27` of cusp `4`. -/
theorem leaf_4_27_346 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (346 : Fin 865) := by
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

/-- Leaf `422` of the square `27` of cusp `4`. -/
theorem leaf_4_27_422 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (422 : Fin 865) := by
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

/-- Leaf `430` of the square `27` of cusp `4`. -/
theorem leaf_4_27_430 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (430 : Fin 865) := by
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

/-- Leaf `701` of the square `27` of cusp `4`. -/
theorem leaf_4_27_701 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (701 : Fin 865) := by
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

/-- Leaf `704` of the square `27` of cusp `4`. -/
theorem leaf_4_27_704 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (704 : Fin 865) := by
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

/-- Leaf `710` of the square `27` of cusp `4`. -/
theorem leaf_4_27_710 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (710 : Fin 865) := by
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

/-- Leaf `713` of the square `27` of cusp `4`. -/
theorem leaf_4_27_713 :
    Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (713 : Fin 865) := by
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

/-- Leaf `90` of the square `28` of cusp `4`. -/
theorem leaf_4_28_90 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (90 : Fin 865) := by
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

/-- Leaf `299` of the square `28` of cusp `4`. -/
theorem leaf_4_28_299 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (299 : Fin 865) := by
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

/-- Leaf `351` of the square `28` of cusp `4`. -/
theorem leaf_4_28_351 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (351 : Fin 865) := by
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

/-- Leaf `434` of the square `28` of cusp `4`. -/
theorem leaf_4_28_434 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (434 : Fin 865) := by
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

/-- Leaf `442` of the square `28` of cusp `4`. -/
theorem leaf_4_28_442 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (442 : Fin 865) := by
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

/-- Leaf `624` of the square `28` of cusp `4`. -/
theorem leaf_4_28_624 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (624 : Fin 865) := by
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

/-- Leaf `647` of the square `28` of cusp `4`. -/
theorem leaf_4_28_647 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (647 : Fin 865) := by
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

/-- Leaf `653` of the square `28` of cusp `4`. -/
theorem leaf_4_28_653 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (653 : Fin 865) := by
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

/-- Leaf `656` of the square `28` of cusp `4`. -/
theorem leaf_4_28_656 :
    Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (656 : Fin 865) := by
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

/-- Leaf `97` of the square `31` of cusp `4`. -/
theorem leaf_4_31_97 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (97 : Fin 865) := by
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

/-- Leaf `239` of the square `31` of cusp `4`. -/
theorem leaf_4_31_239 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (239 : Fin 865) := by
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

/-- Leaf `395` of the square `31` of cusp `4`. -/
theorem leaf_4_31_395 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (395 : Fin 865) := by
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

/-- Leaf `450` of the square `31` of cusp `4`. -/
theorem leaf_4_31_450 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (450 : Fin 865) := by
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

/-- Leaf `458` of the square `31` of cusp `4`. -/
theorem leaf_4_31_458 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (458 : Fin 865) := by
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

/-- Leaf `663` of the square `31` of cusp `4`. -/
theorem leaf_4_31_663 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (663 : Fin 865) := by
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

/-- Leaf `686` of the square `31` of cusp `4`. -/
theorem leaf_4_31_686 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (686 : Fin 865) := by
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

/-- Leaf `692` of the square `31` of cusp `4`. -/
theorem leaf_4_31_692 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (692 : Fin 865) := by
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

/-- Leaf `695` of the square `31` of cusp `4`. -/
theorem leaf_4_31_695 :
    Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (695 : Fin 865) := by
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

/-- Leaf `84` of the square `33` of cusp `4`. -/
theorem leaf_4_33_84 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (84 : Fin 865) := by
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

/-- Leaf `202` of the square `33` of cusp `4`. -/
theorem leaf_4_33_202 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (202 : Fin 865) := by
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

/-- Leaf `322` of the square `33` of cusp `4`. -/
theorem leaf_4_33_322 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (322 : Fin 865) := by
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

/-- Leaf `423` of the square `33` of cusp `4`. -/
theorem leaf_4_33_423 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (423 : Fin 865) := by
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

/-- Leaf `431` of the square `33` of cusp `4`. -/
theorem leaf_4_33_431 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (431 : Fin 865) := by
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

/-- Leaf `705` of the square `33` of cusp `4`. -/
theorem leaf_4_33_705 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (705 : Fin 865) := by
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

/-- Leaf `839` of the square `33` of cusp `4`. -/
theorem leaf_4_33_839 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (839 : Fin 865) := by
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

/-- Leaf `845` of the square `33` of cusp `4`. -/
theorem leaf_4_33_845 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (845 : Fin 865) := by
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

/-- Leaf `848` of the square `33` of cusp `4`. -/
theorem leaf_4_33_848 :
    Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (848 : Fin 865) := by
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

/-- Leaf `92` of the square `34` of cusp `4`. -/
theorem leaf_4_34_92 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (92 : Fin 865) := by
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

/-- Leaf `267` of the square `34` of cusp `4`. -/
theorem leaf_4_34_267 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (267 : Fin 865) := by
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

/-- Leaf `327` of the square `34` of cusp `4`. -/
theorem leaf_4_34_327 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (327 : Fin 865) := by
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

/-- Leaf `435` of the square `34` of cusp `4`. -/
theorem leaf_4_34_435 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (435 : Fin 865) := by
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

/-- Leaf `443` of the square `34` of cusp `4`. -/
theorem leaf_4_34_443 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (443 : Fin 865) := by
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

/-- Leaf `648` of the square `34` of cusp `4`. -/
theorem leaf_4_34_648 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (648 : Fin 865) := by
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

/-- Leaf `774` of the square `34` of cusp `4`. -/
theorem leaf_4_34_774 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (774 : Fin 865) := by
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

/-- Leaf `797` of the square `34` of cusp `4`. -/
theorem leaf_4_34_797 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (797 : Fin 865) := by
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

/-- Leaf `800` of the square `34` of cusp `4`. -/
theorem leaf_4_34_800 :
    Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (800 : Fin 865) := by
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

/-- Leaf `99` of the square `37` of cusp `4`. -/
theorem leaf_4_37_99 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (99 : Fin 865) := by
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

/-- Leaf `207` of the square `37` of cusp `4`. -/
theorem leaf_4_37_207 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (207 : Fin 865) := by
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

/-- Leaf `371` of the square `37` of cusp `4`. -/
theorem leaf_4_37_371 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (371 : Fin 865) := by
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

/-- Leaf `451` of the square `37` of cusp `4`. -/
theorem leaf_4_37_451 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (451 : Fin 865) := by
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

/-- Leaf `459` of the square `37` of cusp `4`. -/
theorem leaf_4_37_459 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (459 : Fin 865) := by
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

/-- Leaf `687` of the square `37` of cusp `4`. -/
theorem leaf_4_37_687 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (687 : Fin 865) := by
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

/-- Leaf `807` of the square `37` of cusp `4`. -/
theorem leaf_4_37_807 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (807 : Fin 865) := by
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

/-- Leaf `830` of the square `37` of cusp `4`. -/
theorem leaf_4_37_830 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (830 : Fin 865) := by
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

/-- Leaf `833` of the square `37` of cusp `4`. -/
theorem leaf_4_37_833 :
    Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (833 : Fin 865) := by
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

/-- Leaf `83` of the square `40` of cusp `4`. -/
theorem leaf_4_40_83 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (83 : Fin 865) := by
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

/-- Leaf `235` of the square `40` of cusp `4`. -/
theorem leaf_4_40_235 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (235 : Fin 865) := by
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

/-- Leaf `347` of the square `40` of cusp `4`. -/
theorem leaf_4_40_347 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (347 : Fin 865) := by
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

/-- Leaf `418` of the square `40` of cusp `4`. -/
theorem leaf_4_40_418 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (418 : Fin 865) := by
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

/-- Leaf `426` of the square `40` of cusp `4`. -/
theorem leaf_4_40_426 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (426 : Fin 865) := by
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

/-- Leaf `702` of the square `40` of cusp `4`. -/
theorem leaf_4_40_702 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (702 : Fin 865) := by
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

/-- Leaf `719` of the square `40` of cusp `4`. -/
theorem leaf_4_40_719 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (719 : Fin 865) := by
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

/-- Leaf `725` of the square `40` of cusp `4`. -/
theorem leaf_4_40_725 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (725 : Fin 865) := by
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

/-- Leaf `728` of the square `40` of cusp `4`. -/
theorem leaf_4_40_728 :
    Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (728 : Fin 865) := by
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

/-- Leaf `85` of the square `44` of cusp `4`. -/
theorem leaf_4_44_85 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (85 : Fin 865) := by
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

/-- Leaf `203` of the square `44` of cusp `4`. -/
theorem leaf_4_44_203 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (203 : Fin 865) := by
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

/-- Leaf `323` of the square `44` of cusp `4`. -/
theorem leaf_4_44_323 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (323 : Fin 865) := by
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

/-- Leaf `419` of the square `44` of cusp `4`. -/
theorem leaf_4_44_419 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (419 : Fin 865) := by
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

/-- Leaf `427` of the square `44` of cusp `4`. -/
theorem leaf_4_44_427 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (427 : Fin 865) := by
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

/-- Leaf `720` of the square `44` of cusp `4`. -/
theorem leaf_4_44_720 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (720 : Fin 865) := by
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

/-- Leaf `840` of the square `44` of cusp `4`. -/
theorem leaf_4_44_840 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (840 : Fin 865) := by
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

/-- Leaf `857` of the square `44` of cusp `4`. -/
theorem leaf_4_44_857 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (857 : Fin 865) := by
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

/-- Leaf `860` of the square `44` of cusp `4`. -/
theorem leaf_4_44_860 :
    Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (860 : Fin 865) := by
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

/-- The chart identity of the flag `(578,302,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_578_302 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_578_302 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (578 : Fin 865)
      exact leaf_4_16_578
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (302 : Fin 865)
      exact leaf_4_16_302
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] fl_4_16_578_302 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_578_302) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_578_302)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_578_302
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_302) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(593,302,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_593_302 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_593_302 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (593 : Fin 865)
      exact leaf_4_16_593
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (302 : Fin 865)
      exact leaf_4_16_302
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ] fl_4_16_593_302 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_593_302) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_593_302)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_593_302
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_302) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(578,398,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_578_398 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_578_398 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (578 : Fin 865)
      exact leaf_4_16_578
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (398 : Fin 865)
      exact leaf_4_16_398
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_578_398 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_578_398) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_578_398)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_578_398
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_578_398) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(596,398,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_596_398 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_596_398 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (596 : Fin 865)
      exact leaf_4_16_596
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (398 : Fin 865)
      exact leaf_4_16_398
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_596_398 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_596_398) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_596_398)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_596_398
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_398) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(587,470,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_587_470 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_587_470 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (587 : Fin 865)
      exact leaf_4_16_587
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (470 : Fin 865)
      exact leaf_4_16_470
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_587_470 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_587_470) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_587_470)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_587_470
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_470) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(593,470,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_593_470 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_593_470 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (593 : Fin 865)
      exact leaf_4_16_593
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (470 : Fin 865)
      exact leaf_4_16_470
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ] fl_4_16_593_470 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_593_470) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_593_470)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_593_470
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_593_470) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(587,478,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_587_478 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_587_478 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (587 : Fin 865)
      exact leaf_4_16_587
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (478 : Fin 865)
      exact leaf_4_16_478
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] fl_4_16_587_478 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_587_478) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_587_478)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_587_478
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_587_478) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(596,478,103)` of the square `16` of cusp `4`. -/
theorem ch_4_16_596_478 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 16 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 16 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 16 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_16_596_478 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (596 : Fin 865)
      exact leaf_4_16_596
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (478 : Fin 865)
      exact leaf_4_16_478
    · show Work.RTOwed.kleinPt 16 (slabL 4 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (103 : Fin 865)
      exact leaf_4_16_103
  have hchart := cSimp_eq_chiRep 4 (a := 16) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ] fl_4_16_596_478 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_16_596_478) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (103 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_16_596_478)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨103⟩ : QbarCW.Cell) fl_4_16_596_478
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨27, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (103 : Fin 865)) fl_4_16_596_478) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(734,270,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_734_270 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_734_270 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (734 : Fin 865)
      exact leaf_4_17_734
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (270 : Fin 865)
      exact leaf_4_17_270
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_734_270 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_734_270) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_734_270)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_734_270
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_270) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(746,270,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_746_270 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_746_270 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (746 : Fin 865)
      exact leaf_4_17_746
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (270 : Fin 865)
      exact leaf_4_17_270
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_746_270 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (0) (1/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_746_270) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_746_270)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_746_270
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_270) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(734,374,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_734_374 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_734_374 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (734 : Fin 865)
      exact leaf_4_17_734
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (374 : Fin 865)
      exact leaf_4_17_374
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_734_374 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_734_374) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_734_374)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_734_374
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_734_374) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(749,374,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_749_374 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_749_374 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (749 : Fin 865)
      exact leaf_4_17_749
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (374 : Fin 865)
      exact leaf_4_17_374
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_749_374 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_749_374) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_749_374)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_749_374
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_374) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(588,471,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_588_471 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_588_471 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (588 : Fin 865)
      exact leaf_4_17_588
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (471 : Fin 865)
      exact leaf_4_17_471
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_588_471 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_588_471) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_588_471)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_588_471
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_471) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(746,471,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_746_471 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_746_471 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (746 : Fin 865)
      exact leaf_4_17_746
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (471 : Fin 865)
      exact leaf_4_17_471
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ] fl_4_17_746_471 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_746_471) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_746_471)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_746_471
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_746_471) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(588,479,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_588_479 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_588_479 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (588 : Fin 865)
      exact leaf_4_17_588
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (479 : Fin 865)
      exact leaf_4_17_479
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_588_479 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_588_479) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_588_479)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_588_479
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_588_479) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(749,479,105)` of the square `17` of cusp `4`. -/
theorem ch_4_17_749_479 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 17 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 17 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 17 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_17_749_479 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (749 : Fin 865)
      exact leaf_4_17_749
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (479 : Fin 865)
      exact leaf_4_17_479
    · show Work.RTOwed.kleinPt 17 (slabL 4 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (105 : Fin 865)
      exact leaf_4_17_105
  have hchart := cSimp_eq_chiRep 4 (a := 17) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ] fl_4_17_749_479 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_17_749_479) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (105 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_17_749_479)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨105⟩ : QbarCW.Cell) fl_4_17_749_479
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨25, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (105 : Fin 865)) fl_4_17_749_479) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(623,298,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_623_298 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_623_298 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (623 : Fin 865)
      exact leaf_4_18_623
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (298 : Fin 865)
      exact leaf_4_18_298
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_623_298 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_623_298) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_623_298)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_623_298
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_298) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(635,298,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_635_298 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_635_298 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (635 : Fin 865)
      exact leaf_4_18_635
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (298 : Fin 865)
      exact leaf_4_18_298
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_635_298 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_635_298) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_635_298)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_635_298
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_298) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(623,350,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_623_350 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_623_350 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (623 : Fin 865)
      exact leaf_4_18_623
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (350 : Fin 865)
      exact leaf_4_18_350
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_623_350 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_623_350) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_623_350)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_623_350
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_623_350) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(638,350,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_638_350 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_638_350 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (638 : Fin 865)
      exact leaf_4_18_638
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (350 : Fin 865)
      exact leaf_4_18_350
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_638_350 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_638_350) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_638_350)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_638_350
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_350) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(629,438,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_629_438 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_629_438 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (629 : Fin 865)
      exact leaf_4_18_629
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (438 : Fin 865)
      exact leaf_4_18_438
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_629_438 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_629_438) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_629_438)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_629_438
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_438) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(635,438,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_635_438 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_635_438 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (635 : Fin 865)
      exact leaf_4_18_635
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (438 : Fin 865)
      exact leaf_4_18_438
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ] fl_4_18_635_438 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_635_438) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_635_438)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_635_438
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_635_438) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(629,446,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_629_446 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_629_446 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (629 : Fin 865)
      exact leaf_4_18_629
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (446 : Fin 865)
      exact leaf_4_18_446
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_629_446 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_629_446) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_629_446)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_629_446
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_629_446) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(638,446,89)` of the square `18` of cusp `4`. -/
theorem ch_4_18_638_446 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 18 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 18 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 18 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_18_638_446 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (638 : Fin 865)
      exact leaf_4_18_638
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (446 : Fin 865)
      exact leaf_4_18_446
    · show Work.RTOwed.kleinPt 18 (slabL 4 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (89 : Fin 865)
      exact leaf_4_18_89
  have hchart := cSimp_eq_chiRep 4 (a := 18) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ] fl_4_18_638_446 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_18_638_446) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (89 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_18_638_446)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨89⟩ : QbarCW.Cell) fl_4_18_638_446
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨39, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (89 : Fin 865)) fl_4_18_638_446) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(662,238,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_662_238 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_662_238 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (662 : Fin 865)
      exact leaf_4_20_662
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (238 : Fin 865)
      exact leaf_4_20_238
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_662_238 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_662_238) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_662_238)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_662_238
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_238) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(674,238,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_674_238 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_674_238 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (674 : Fin 865)
      exact leaf_4_20_674
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (238 : Fin 865)
      exact leaf_4_20_238
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_674_238 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_674_238) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_674_238)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_674_238
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_238) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(662,394,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_662_394 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_662_394 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (662 : Fin 865)
      exact leaf_4_20_662
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (394 : Fin 865)
      exact leaf_4_20_394
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_662_394 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_662_394) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_662_394)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_662_394
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_662_394) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(677,394,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_677_394 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_677_394 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (677 : Fin 865)
      exact leaf_4_20_677
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (394 : Fin 865)
      exact leaf_4_20_394
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_677_394 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_677_394) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_677_394)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_677_394
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_394) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(668,454,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_668_454 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_668_454 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (668 : Fin 865)
      exact leaf_4_20_668
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (454 : Fin 865)
      exact leaf_4_20_454
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_668_454 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_668_454) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_668_454)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_668_454
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_454) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(674,454,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_674_454 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_674_454 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (674 : Fin 865)
      exact leaf_4_20_674
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (454 : Fin 865)
      exact leaf_4_20_454
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ] fl_4_20_674_454 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (0) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_674_454) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_674_454)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_674_454
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_674_454) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(668,462,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_668_462 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_668_462 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (668 : Fin 865)
      exact leaf_4_20_668
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (462 : Fin 865)
      exact leaf_4_20_462
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_668_462 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_668_462) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_668_462)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_668_462
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_668_462) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(677,462,96)` of the square `20` of cusp `4`. -/
theorem ch_4_20_677_462 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 20 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 20 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 20 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_20_677_462 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (677 : Fin 865)
      exact leaf_4_20_677
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (462 : Fin 865)
      exact leaf_4_20_462
    · show Work.RTOwed.kleinPt 20 (slabL 4 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (96 : Fin 865)
      exact leaf_4_20_96
  have hchart := cSimp_eq_chiRep 4 (a := 20) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ] fl_4_20_677_462 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_20_677_462) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (96 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_20_677_462)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨96⟩ : QbarCW.Cell) fl_4_20_677_462
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨33, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (96 : Fin 865)) fl_4_20_677_462) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(579,303,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_579_303 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_579_303 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (579 : Fin 865)
      exact leaf_4_21_579
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (303 : Fin 865)
      exact leaf_4_21_303
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_579_303 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_579_303) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_579_303)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_579_303
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_303) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(614,303,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_614_303 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_614_303 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (614 : Fin 865)
      exact leaf_4_21_614
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (303 : Fin 865)
      exact leaf_4_21_303
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_614_303 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (0) (-3/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_614_303) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_614_303)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_614_303
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_303) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(579,399,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_579_399 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_579_399 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (579 : Fin 865)
      exact leaf_4_21_579
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (399 : Fin 865)
      exact leaf_4_21_399
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_579_399 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_579_399) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_579_399)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_579_399
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_579_399) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(617,399,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_617_399 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_617_399 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (617 : Fin 865)
      exact leaf_4_21_617
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (399 : Fin 865)
      exact leaf_4_21_399
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_617_399 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_617_399) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_617_399)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_617_399
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_399) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(608,466,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_608_466 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_608_466 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (608 : Fin 865)
      exact leaf_4_21_608
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (466 : Fin 865)
      exact leaf_4_21_466
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_608_466 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_608_466) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_608_466)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_608_466
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_466) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(614,466,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_614_466 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_614_466 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (614 : Fin 865)
      exact leaf_4_21_614
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (466 : Fin 865)
      exact leaf_4_21_466
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ] fl_4_21_614_466 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_614_466) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_614_466)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_614_466
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_614_466) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(608,474,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_608_474 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_608_474 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (608 : Fin 865)
      exact leaf_4_21_608
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (474 : Fin 865)
      exact leaf_4_21_474
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_608_474 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_608_474) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_608_474)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_608_474
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_608_474) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(617,474,104)` of the square `21` of cusp `4`. -/
theorem ch_4_21_617_474 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 21 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 21 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 21 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_21_617_474 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (617 : Fin 865)
      exact leaf_4_21_617
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (474 : Fin 865)
      exact leaf_4_21_474
    · show Work.RTOwed.kleinPt 21 (slabL 4 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (104 : Fin 865)
      exact leaf_4_21_104
  have hchart := cSimp_eq_chiRep 4 (a := 21) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ] fl_4_21_617_474 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (0) (-1/8) 1, slabPt (0) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_21_617_474) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (104 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_21_617_474)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨104⟩ : QbarCW.Cell) fl_4_21_617_474
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨26, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (104 : Fin 865)) fl_4_21_617_474) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(773,266,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_773_266 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_773_266 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (773 : Fin 865)
      exact leaf_4_22_773
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (266 : Fin 865)
      exact leaf_4_22_266
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_773_266 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_773_266) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_773_266)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_773_266
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_266) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(782,266,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_782_266 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_782_266 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (782 : Fin 865)
      exact leaf_4_22_782
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (266 : Fin 865)
      exact leaf_4_22_266
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_782_266 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/4) (1/8) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_782_266) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_782_266)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_782_266
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_266) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(773,326,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_773_326 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_773_326 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (773 : Fin 865)
      exact leaf_4_22_773
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (326 : Fin 865)
      exact leaf_4_22_326
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_773_326 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (1/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_773_326) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_773_326)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_773_326
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_773_326) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(785,326,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_785_326 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_785_326 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (785 : Fin 865)
      exact leaf_4_22_785
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (326 : Fin 865)
      exact leaf_4_22_326
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_785_326 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/4) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_785_326) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_785_326)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_785_326
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_326) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(630,439,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_630_439 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_630_439 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (630 : Fin 865)
      exact leaf_4_22_630
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (439 : Fin 865)
      exact leaf_4_22_439
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_630_439 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_630_439) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_630_439)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_630_439
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨630⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨630⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide) (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_439) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(782,439,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_782_439 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_782_439 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (782 : Fin 865)
      exact leaf_4_22_782
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (439 : Fin 865)
      exact leaf_4_22_439
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_782_439 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_782_439) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_782_439)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_782_439
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨439⟩ : QbarCell) from by decide) (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨439⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_782_439) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(630,447,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_630_447 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_630_447 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (630 : Fin 865)
      exact leaf_4_22_630
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (447 : Fin 865)
      exact leaf_4_22_447
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_630_447 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_630_447) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_630_447)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_630_447
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨630⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨630⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide) (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_630_447) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(785,447,91)` of the square `22` of cusp `4`. -/
theorem ch_4_22_785_447 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 22 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 22 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 22 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_22_785_447 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (785 : Fin 865)
      exact leaf_4_22_785
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (447 : Fin 865)
      exact leaf_4_22_447
    · show Work.RTOwed.kleinPt 22 (slabL 4 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (91 : Fin 865)
      exact leaf_4_22_91
  have hchart := cSimp_eq_chiRep 4 (a := 22) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ] fl_4_22_785_447 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_22_785_447) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (91 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_22_785_447)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨91⟩ : QbarCW.Cell) fl_4_22_785_447
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨447⟩ : QbarCell) from by decide) (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨447⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨37, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (91 : Fin 865)) fl_4_22_785_447) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(806,206,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_806_206 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_806_206 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (806 : Fin 865)
      exact leaf_4_24_806
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (206 : Fin 865)
      exact leaf_4_24_206
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_806_206 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_806_206) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_806_206)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_806_206
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨806⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨806⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide) (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_206) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(815,206,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_815_206 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_815_206 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (815 : Fin 865)
      exact leaf_4_24_815
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (206 : Fin 865)
      exact leaf_4_24_206
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_815_206 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/4) (1/8) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_815_206) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_815_206)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_815_206
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨815⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨815⟩ : QbarCell) < (⟨206⟩ : QbarCell) from by decide) (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨206⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_206) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(806,370,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_806_370 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_806_370 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (806 : Fin 865)
      exact leaf_4_24_806
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (370 : Fin 865)
      exact leaf_4_24_370
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_806_370 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (1/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_806_370) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_806_370)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_806_370
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨806⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨806⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide) (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_806_370) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(818,370,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_818_370 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_818_370 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (818 : Fin 865)
      exact leaf_4_24_818
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (370 : Fin 865)
      exact leaf_4_24_370
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_818_370 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_818_370) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_818_370)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_818_370
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨370⟩ : QbarCell) from by decide) (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨370⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_370) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(669,455,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_669_455 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_669_455 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (669 : Fin 865)
      exact leaf_4_24_669
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (455 : Fin 865)
      exact leaf_4_24_455
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_669_455 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_669_455) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_669_455)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_669_455
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide) (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_455) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(815,455,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_815_455 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_815_455 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (815 : Fin 865)
      exact leaf_4_24_815
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (455 : Fin 865)
      exact leaf_4_24_455
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_815_455 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (1/8) 1, slabPt (-1/8) (1/4) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_815_455) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_815_455)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_815_455
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨815⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨815⟩ : QbarCell) < (⟨455⟩ : QbarCell) from by decide) (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨455⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_815_455) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(669,463,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_669_463 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_669_463 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (669 : Fin 865)
      exact leaf_4_24_669
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (463 : Fin 865)
      exact leaf_4_24_463
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_669_463 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_669_463) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_669_463)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_669_463
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨669⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨669⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_669_463) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(818,463,98)` of the square `24` of cusp `4`. -/
theorem ch_4_24_818_463 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 24 := by
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
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 24 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 24 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_24_818_463 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (818 : Fin 865)
      exact leaf_4_24_818
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (463 : Fin 865)
      exact leaf_4_24_463
    · show Work.RTOwed.kleinPt 24 (slabL 4 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (98 : Fin 865)
      exact leaf_4_24_98
  have hchart := cSimp_eq_chiRep 4 (a := 24) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ] fl_4_24_818_463 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_24_818_463) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (98 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_24_818_463)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨98⟩ : QbarCW.Cell) fl_4_24_818_463
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨818⟩ : QbarCell) < (⟨98⟩ : QbarCell) from lt_trans (show (⟨818⟩ : QbarCell) < (⟨463⟩ : QbarCell) from by decide) (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨463⟩ : QbarCell) < (⟨98⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨31, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (98 : Fin 865)) fl_4_24_818_463) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(735,271,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_735_271 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_735_271 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (735 : Fin 865)
      exact leaf_4_25_735
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (271 : Fin 865)
      exact leaf_4_25_271
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] fl_4_25_735_271 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_735_271) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_735_271)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_735_271
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_271) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(764,271,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_764_271 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_764_271 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (764 : Fin 865)
      exact leaf_4_25_764
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (271 : Fin 865)
      exact leaf_4_25_271
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ] fl_4_25_764_271 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (0) (5/8) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_764_271) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_764_271)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_764_271
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨271⟩ : QbarCell) from by decide) (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨271⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_271) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(735,375,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_735_375 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_735_375 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (735 : Fin 865)
      exact leaf_4_25_735
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (375 : Fin 865)
      exact leaf_4_25_375
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] fl_4_25_735_375 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_735_375) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_735_375)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_735_375
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨735⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨735⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_735_375) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(767,375,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_767_375 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_767_375 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (767 : Fin 865)
      exact leaf_4_25_767
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (375 : Fin 865)
      exact leaf_4_25_375
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ] fl_4_25_767_375 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_767_375) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_767_375)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_767_375
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨767⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨767⟩ : QbarCell) < (⟨375⟩ : QbarCell) from by decide) (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨375⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_375) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(609,467,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_609_467 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_609_467 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (609 : Fin 865)
      exact leaf_4_25_609
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (467 : Fin 865)
      exact leaf_4_25_467
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] fl_4_25_609_467 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_609_467) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_609_467)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_609_467
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨609⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨609⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide) (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_467) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(764,467,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_764_467 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_764_467 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (764 : Fin 865)
      exact leaf_4_25_764
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (467 : Fin 865)
      exact leaf_4_25_467
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ] fl_4_25_764_467 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_764_467) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_764_467)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_764_467
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨764⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨764⟩ : QbarCell) < (⟨467⟩ : QbarCell) from by decide) (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨467⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_764_467) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(609,475,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_609_475 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_609_475 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (609 : Fin 865)
      exact leaf_4_25_609
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (475 : Fin 865)
      exact leaf_4_25_475
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] fl_4_25_609_475 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_609_475) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_609_475)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_609_475
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨609⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨609⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide) (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_609_475) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(767,475,106)` of the square `25` of cusp `4`. -/
theorem ch_4_25_767_475 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 25 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 25 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 25 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_25_767_475 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (767 : Fin 865)
      exact leaf_4_25_767
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (475 : Fin 865)
      exact leaf_4_25_475
    · show Work.RTOwed.kleinPt 25 (slabL 4 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (106 : Fin 865)
      exact leaf_4_25_106
  have hchart := cSimp_eq_chiRep 4 (a := 25) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ] fl_4_25_767_475 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (0) (3/8) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_25_767_475) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (106 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_25_767_475)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨106⟩ : QbarCW.Cell) fl_4_25_767_475
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨767⟩ : QbarCell) < (⟨106⟩ : QbarCell) from lt_trans (show (⟨767⟩ : QbarCell) < (⟨475⟩ : QbarCell) from by decide) (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨475⟩ : QbarCell) < (⟨106⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨24, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (106 : Fin 865)) fl_4_25_767_475) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(701,234,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_701_234 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_701_234 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (701 : Fin 865)
      exact leaf_4_27_701
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (234 : Fin 865)
      exact leaf_4_27_234
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] fl_4_27_701_234 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_701_234) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_701_234)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_701_234
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide) (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_234) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(710,234,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_710_234 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_710_234 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (710 : Fin 865)
      exact leaf_4_27_710
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (234 : Fin 865)
      exact leaf_4_27_234
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ] fl_4_27_710_234 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_710_234) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_710_234)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_710_234
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨234⟩ : QbarCell) from by decide) (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨234⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_234) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(701,346,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_701_346 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_701_346 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (701 : Fin 865)
      exact leaf_4_27_701
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (346 : Fin 865)
      exact leaf_4_27_346
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_701_346 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_701_346) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_701_346)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_701_346
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨701⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨701⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_701_346) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(713,346,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_713_346 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_713_346 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (713 : Fin 865)
      exact leaf_4_27_713
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (346 : Fin 865)
      exact leaf_4_27_346
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_713_346 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_713_346) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_713_346)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_713_346
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨346⟩ : QbarCell) from by decide) (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨346⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_346) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(704,422,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_704_422 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_704_422 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (704 : Fin 865)
      exact leaf_4_27_704
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (422 : Fin 865)
      exact leaf_4_27_422
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_704_422 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_704_422) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_704_422)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_704_422
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_422) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(710,422,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_710_422 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_710_422 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (710 : Fin 865)
      exact leaf_4_27_710
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (422 : Fin 865)
      exact leaf_4_27_422
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ] fl_4_27_710_422 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_710_422) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_710_422)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_710_422
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨710⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨710⟩ : QbarCell) < (⟨422⟩ : QbarCell) from by decide) (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨422⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_710_422) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(704,430,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_704_430 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_704_430 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (704 : Fin 865)
      exact leaf_4_27_704
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (430 : Fin 865)
      exact leaf_4_27_430
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] fl_4_27_704_430 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_704_430) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_704_430)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_704_430
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨704⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨704⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_704_430) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(713,430,82)` of the square `27` of cusp `4`. -/
theorem ch_4_27_713_430 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 27 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 27 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 27 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_27_713_430 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (713 : Fin 865)
      exact leaf_4_27_713
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (430 : Fin 865)
      exact leaf_4_27_430
    · show Work.RTOwed.kleinPt 27 (slabL 4 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (82 : Fin 865)
      exact leaf_4_27_82
  have hchart := cSimp_eq_chiRep 4 (a := 27) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ] fl_4_27_713_430 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_27_713_430) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (82 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_27_713_430)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨82⟩ : QbarCW.Cell) fl_4_27_713_430
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨713⟩ : QbarCell) < (⟨82⟩ : QbarCell) from lt_trans (show (⟨713⟩ : QbarCell) < (⟨430⟩ : QbarCell) from by decide) (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨430⟩ : QbarCell) < (⟨82⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨45, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (82 : Fin 865)) fl_4_27_713_430) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(624,299,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_624_299 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_624_299 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (624 : Fin 865)
      exact leaf_4_28_624
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (299 : Fin 865)
      exact leaf_4_28_299
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_624_299 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_624_299) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_624_299)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_624_299
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_299) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(653,299,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_653_299 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_653_299 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (653 : Fin 865)
      exact leaf_4_28_653
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (299 : Fin 865)
      exact leaf_4_28_299
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_653_299 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/4) (-3/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_653_299) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_653_299)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_653_299
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨299⟩ : QbarCell) from by decide) (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨299⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_299) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(624,351,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_624_351 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_624_351 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (624 : Fin 865)
      exact leaf_4_28_624
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (351 : Fin 865)
      exact leaf_4_28_351
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_624_351 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-3/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_624_351) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_624_351)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_624_351
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨624⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨624⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_624_351) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(656,351,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_656_351 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_656_351 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (656 : Fin 865)
      exact leaf_4_28_656
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (351 : Fin 865)
      exact leaf_4_28_351
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_656_351 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_656_351) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_656_351)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_656_351
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨351⟩ : QbarCell) from by decide) (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨351⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_351) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(647,434,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_647_434 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_647_434 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (647 : Fin 865)
      exact leaf_4_28_647
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (434 : Fin 865)
      exact leaf_4_28_434
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_647_434 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_647_434) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_647_434)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_647_434
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_434) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(653,434,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_653_434 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_653_434 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (653 : Fin 865)
      exact leaf_4_28_653
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (434 : Fin 865)
      exact leaf_4_28_434
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_653_434 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_653_434) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_653_434)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_653_434
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨653⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨653⟩ : QbarCell) < (⟨434⟩ : QbarCell) from by decide) (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨434⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_653_434) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(647,442,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_647_442 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_647_442 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (647 : Fin 865)
      exact leaf_4_28_647
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (442 : Fin 865)
      exact leaf_4_28_442
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_647_442 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_647_442) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_647_442)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_647_442
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨647⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨647⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_647_442) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(656,442,90)` of the square `28` of cusp `4`. -/
theorem ch_4_28_656_442 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 28 := by
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
      (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 28 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 28 (slabL 4 (![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_28_656_442 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (656 : Fin 865)
      exact leaf_4_28_656
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (442 : Fin 865)
      exact leaf_4_28_442
    · show Work.RTOwed.kleinPt 28 (slabL 4 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (90 : Fin 865)
      exact leaf_4_28_90
  have hchart := cSimp_eq_chiRep 4 (a := 28) rfl
    ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ] fl_4_28_656_442 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (-1/8) 1, slabPt (1/4) (-1/8) 1, slabPt (1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_28_656_442) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (90 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_28_656_442)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨90⟩ : QbarCW.Cell) fl_4_28_656_442
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨656⟩ : QbarCell) < (⟨90⟩ : QbarCell) from lt_trans (show (⟨656⟩ : QbarCell) < (⟨442⟩ : QbarCell) from by decide) (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨442⟩ : QbarCell) < (⟨90⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨38, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (90 : Fin 865)) fl_4_28_656_442) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(663,239,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_663_239 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_663_239 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (663 : Fin 865)
      exact leaf_4_31_663
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (239 : Fin 865)
      exact leaf_4_31_239
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_663_239 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_663_239) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_663_239)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_663_239
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_239) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(692,239,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_692_239 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_692_239 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (692 : Fin 865)
      exact leaf_4_31_692
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (239 : Fin 865)
      exact leaf_4_31_239
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_692_239 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/4) (-3/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_692_239) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_692_239)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_692_239
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨239⟩ : QbarCell) from by decide) (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨239⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_239) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(663,395,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_663_395 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_663_395 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (663 : Fin 865)
      exact leaf_4_31_663
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (395 : Fin 865)
      exact leaf_4_31_395
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_663_395 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-3/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_663_395) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_663_395)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_663_395
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨663⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨663⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_663_395) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(695,395,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_695_395 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_695_395 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (695 : Fin 865)
      exact leaf_4_31_695
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (395 : Fin 865)
      exact leaf_4_31_395
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_695_395 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-3/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_695_395) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_695_395)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_695_395
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨395⟩ : QbarCell) from by decide) (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨395⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_395) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(686,450,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_686_450 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_686_450 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (686 : Fin 865)
      exact leaf_4_31_686
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (450 : Fin 865)
      exact leaf_4_31_450
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_686_450 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_686_450) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_686_450)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_686_450
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_450) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(692,450,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_692_450 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_692_450 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (692 : Fin 865)
      exact leaf_4_31_692
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (450 : Fin 865)
      exact leaf_4_31_450
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_692_450 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-3/8) 1, slabPt (-1/8) (-1/4) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_692_450) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_692_450)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_692_450
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨692⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨692⟩ : QbarCell) < (⟨450⟩ : QbarCell) from by decide) (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨450⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_692_450) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(686,458,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_686_458 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_686_458 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (686 : Fin 865)
      exact leaf_4_31_686
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (458 : Fin 865)
      exact leaf_4_31_458
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_686_458 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_686_458) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_686_458)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_686_458
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨686⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨686⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_686_458) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(695,458,97)` of the square `31` of cusp `4`. -/
theorem ch_4_31_695_458 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 31 := by
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
      (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 31 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 31 (slabL 4 (![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_31_695_458 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (695 : Fin 865)
      exact leaf_4_31_695
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (458 : Fin 865)
      exact leaf_4_31_458
    · show Work.RTOwed.kleinPt 31 (slabL 4 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (97 : Fin 865)
      exact leaf_4_31_97
  have hchart := cSimp_eq_chiRep 4 (a := 31) rfl
    ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ] fl_4_31_695_458 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (-1/8) 1, slabPt (-1/4) (-1/8) 1, slabPt (-1/4) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_31_695_458) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (97 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_31_695_458)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨97⟩ : QbarCW.Cell) fl_4_31_695_458
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨695⟩ : QbarCell) < (⟨97⟩ : QbarCell) from lt_trans (show (⟨695⟩ : QbarCell) < (⟨458⟩ : QbarCell) from by decide) (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨458⟩ : QbarCell) < (⟨97⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨32, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (97 : Fin 865)) fl_4_31_695_458) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(839,202,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_839_202 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_839_202 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (839 : Fin 865)
      exact leaf_4_33_839
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (202 : Fin 865)
      exact leaf_4_33_202
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_839_202 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_839_202) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_839_202)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_839_202
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_202) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(845,202,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_845_202 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_845_202 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (845 : Fin 865)
      exact leaf_4_33_845
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (202 : Fin 865)
      exact leaf_4_33_202
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_845_202 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (1/2) (1/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_845_202) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_845_202)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_845_202
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨202⟩ : QbarCell) from by decide) (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨202⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_202) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(839,322,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_839_322 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_839_322 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (839 : Fin 865)
      exact leaf_4_33_839
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (322 : Fin 865)
      exact leaf_4_33_322
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_839_322 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (1/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_839_322) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_839_322)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_839_322
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨839⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨839⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_839_322) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(848,322,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_848_322 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_848_322 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (848 : Fin 865)
      exact leaf_4_33_848
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (322 : Fin 865)
      exact leaf_4_33_322
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_848_322 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_848_322) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_848_322)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_848_322
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨322⟩ : QbarCell) from by decide) (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨322⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_322) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(705,423,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_705_423 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_705_423 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (705 : Fin 865)
      exact leaf_4_33_705
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (423 : Fin 865)
      exact leaf_4_33_423
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_705_423 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_705_423) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_705_423)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_705_423
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_423) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(845,423,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_845_423 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_845_423 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (845 : Fin 865)
      exact leaf_4_33_845
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (423 : Fin 865)
      exact leaf_4_33_423
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_845_423 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (1/8) 1, slabPt (3/8) (1/4) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_845_423) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_845_423)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_845_423
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨845⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨845⟩ : QbarCell) < (⟨423⟩ : QbarCell) from by decide) (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨423⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_845_423) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(705,431,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_705_431 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_705_431 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (705 : Fin 865)
      exact leaf_4_33_705
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (431 : Fin 865)
      exact leaf_4_33_431
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_705_431 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_705_431) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_705_431)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_705_431
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨705⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨705⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_705_431) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(848,431,84)` of the square `33` of cusp `4`. -/
theorem ch_4_33_848_431 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 33 := by
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
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 33 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 33 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_33_848_431 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (848 : Fin 865)
      exact leaf_4_33_848
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (431 : Fin 865)
      exact leaf_4_33_431
    · show Work.RTOwed.kleinPt 33 (slabL 4 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (84 : Fin 865)
      exact leaf_4_33_84
  have hchart := cSimp_eq_chiRep 4 (a := 33) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ] fl_4_33_848_431 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_33_848_431) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (84 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_33_848_431)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨84⟩ : QbarCW.Cell) fl_4_33_848_431
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨848⟩ : QbarCell) < (⟨84⟩ : QbarCell) from lt_trans (show (⟨848⟩ : QbarCell) < (⟨431⟩ : QbarCell) from by decide) (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨431⟩ : QbarCell) < (⟨84⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨43, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (84 : Fin 865)) fl_4_33_848_431) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(774,267,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_774_267 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_774_267 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (774 : Fin 865)
      exact leaf_4_34_774
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (267 : Fin 865)
      exact leaf_4_34_267
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_774_267 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_774_267) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_774_267)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_774_267
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_267) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(797,267,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_797_267 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_797_267 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (797 : Fin 865)
      exact leaf_4_34_797
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (267 : Fin 865)
      exact leaf_4_34_267
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_797_267 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/4) (5/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_797_267) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_797_267)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_797_267
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨267⟩ : QbarCell) from by decide) (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨267⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_267) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(774,327,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_774_327 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_774_327 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (774 : Fin 865)
      exact leaf_4_34_774
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (327 : Fin 865)
      exact leaf_4_34_327
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_774_327 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (5/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_774_327) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_774_327)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_774_327
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨774⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨774⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_774_327) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(800,327,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_800_327 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_800_327 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (800 : Fin 865)
      exact leaf_4_34_800
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (327 : Fin 865)
      exact leaf_4_34_327
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_800_327 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_800_327) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_800_327)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_800_327
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨327⟩ : QbarCell) from by decide) (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨327⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_327) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(648,435,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_648_435 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_648_435 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (648 : Fin 865)
      exact leaf_4_34_648
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (435 : Fin 865)
      exact leaf_4_34_435
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_648_435 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_648_435) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_648_435)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_648_435
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_435) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(797,435,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_797_435 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_797_435 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (797 : Fin 865)
      exact leaf_4_34_797
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (435 : Fin 865)
      exact leaf_4_34_435
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_797_435 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_797_435) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_797_435)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_797_435
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨797⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨797⟩ : QbarCell) < (⟨435⟩ : QbarCell) from by decide) (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨435⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_797_435) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(648,443,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_648_443 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_648_443 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (648 : Fin 865)
      exact leaf_4_34_648
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (443 : Fin 865)
      exact leaf_4_34_443
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_648_443 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_648_443) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_648_443)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_648_443
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨648⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨648⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_648_443) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(800,443,92)` of the square `34` of cusp `4`. -/
theorem ch_4_34_800_443 :
    cChain 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 34 := by
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
      (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 34 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 34 (slabL 4 (![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_34_800_443 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (800 : Fin 865)
      exact leaf_4_34_800
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (443 : Fin 865)
      exact leaf_4_34_443
    · show Work.RTOwed.kleinPt 34 (slabL 4 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (92 : Fin 865)
      exact leaf_4_34_92
  have hchart := cSimp_eq_chiRep 4 (a := 34) rfl
    ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ] fl_4_34_800_443 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (1/8) (3/8) 1, slabPt (1/4) (3/8) 1, slabPt (1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_34_800_443) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (92 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_34_800_443)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨92⟩ : QbarCW.Cell) fl_4_34_800_443
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨800⟩ : QbarCell) < (⟨92⟩ : QbarCell) from lt_trans (show (⟨800⟩ : QbarCell) < (⟨443⟩ : QbarCell) from by decide) (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨443⟩ : QbarCell) < (⟨92⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨36, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (92 : Fin 865)) fl_4_34_800_443) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(807,207,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_807_207 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_807_207 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (807 : Fin 865)
      exact leaf_4_37_807
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (207 : Fin 865)
      exact leaf_4_37_207
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_807_207 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_807_207) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_807_207)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_807_207
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_207) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(830,207,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_830_207 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_830_207 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (830 : Fin 865)
      exact leaf_4_37_830
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (207 : Fin 865)
      exact leaf_4_37_207
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_830_207 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/4) (5/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_830_207) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_830_207)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_830_207
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨207⟩ : QbarCell) from by decide) (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨207⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_207) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(807,371,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_807_371 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_807_371 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (807 : Fin 865)
      exact leaf_4_37_807
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (371 : Fin 865)
      exact leaf_4_37_371
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_807_371 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (5/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_807_371) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_807_371)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_807_371
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨807⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨807⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_807_371) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(833,371,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_833_371 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_833_371 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (833 : Fin 865)
      exact leaf_4_37_833
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (371 : Fin 865)
      exact leaf_4_37_371
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_833_371 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-3/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_833_371) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_833_371)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_833_371
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨371⟩ : QbarCell) from by decide) (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨371⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_371) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(687,451,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_687_451 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_687_451 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (687 : Fin 865)
      exact leaf_4_37_687
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (451 : Fin 865)
      exact leaf_4_37_451
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_687_451 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_687_451) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_687_451)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_687_451
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_451) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(830,451,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_830_451 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_830_451 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (830 : Fin 865)
      exact leaf_4_37_830
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (451 : Fin 865)
      exact leaf_4_37_451
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_830_451 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (5/8) 1, slabPt (-1/8) (1/2) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_830_451) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_830_451)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_830_451
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨830⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨830⟩ : QbarCell) < (⟨451⟩ : QbarCell) from by decide) (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨451⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_830_451) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(687,459,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_687_459 :
    cChain 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_687_459 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (687 : Fin 865)
      exact leaf_4_37_687
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (459 : Fin 865)
      exact leaf_4_37_459
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_687_459 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-1/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_687_459) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_687_459)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_687_459
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨687⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨687⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_687_459) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(833,459,99)` of the square `37` of cusp `4`. -/
theorem ch_4_37_833_459 :
    cChain 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 37 := by
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
      (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 37 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 37 (slabL 4 (![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_37_833_459 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (833 : Fin 865)
      exact leaf_4_37_833
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (459 : Fin 865)
      exact leaf_4_37_459
    · show Work.RTOwed.kleinPt 37 (slabL 4 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (99 : Fin 865)
      exact leaf_4_37_99
  have hchart := cSimp_eq_chiRep 4 (a := 37) rfl
    ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ] fl_4_37_833_459 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (-3/8) (3/8) 1, slabPt (-1/4) (3/8) 1, slabPt (-1/4) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_37_833_459) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (99 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_37_833_459)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨99⟩ : QbarCW.Cell) fl_4_37_833_459
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨833⟩ : QbarCell) < (⟨99⟩ : QbarCell) from lt_trans (show (⟨833⟩ : QbarCell) < (⟨459⟩ : QbarCell) from by decide) (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨459⟩ : QbarCell) < (⟨99⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨30, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (99 : Fin 865)) fl_4_37_833_459) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(702,235,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_702_235 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_702_235 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (702 : Fin 865)
      exact leaf_4_40_702
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (235 : Fin 865)
      exact leaf_4_40_235
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_702_235 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_702_235) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_702_235)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_702_235
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_235) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(725,235,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_725_235 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_725_235 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (725 : Fin 865)
      exact leaf_4_40_725
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (235 : Fin 865)
      exact leaf_4_40_235
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_725_235 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (1/2) (-3/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_725_235) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_725_235)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_725_235
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨235⟩ : QbarCell) from by decide) (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨235⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_235) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(702,347,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_702_347 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_702_347 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (702 : Fin 865)
      exact leaf_4_40_702
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (347 : Fin 865)
      exact leaf_4_40_347
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_702_347 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-3/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_702_347) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_702_347)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_702_347
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨702⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨702⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_702_347) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(728,347,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_728_347 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_728_347 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (728 : Fin 865)
      exact leaf_4_40_728
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (347 : Fin 865)
      exact leaf_4_40_347
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_728_347 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (5/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_728_347) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_728_347)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_728_347
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨347⟩ : QbarCell) from by decide) (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨347⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_347) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(719,418,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_719_418 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_719_418 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (719 : Fin 865)
      exact leaf_4_40_719
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (418 : Fin 865)
      exact leaf_4_40_418
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_719_418 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_719_418) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_719_418)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_719_418
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_418) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(725,418,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_725_418 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_725_418 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (725 : Fin 865)
      exact leaf_4_40_725
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (418 : Fin 865)
      exact leaf_4_40_418
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_725_418 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-3/8) 1, slabPt (3/8) (-1/4) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_725_418) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_725_418)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_725_418
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨725⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨725⟩ : QbarCell) < (⟨418⟩ : QbarCell) from by decide) (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨418⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_725_418) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(719,426,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_719_426 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_719_426 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (3/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (719 : Fin 865)
      exact leaf_4_40_719
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (426 : Fin 865)
      exact leaf_4_40_426
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_719_426 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_719_426) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_719_426)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_719_426
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨719⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨719⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_719_426) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(728,426,83)` of the square `40` of cusp `4`. -/
theorem ch_4_40_728_426 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 40 := by
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
      (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 40 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 40 (slabL 4 (![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_40_728_426 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (5/8) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (728 : Fin 865)
      exact leaf_4_40_728
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (426 : Fin 865)
      exact leaf_4_40_426
    · show Work.RTOwed.kleinPt 40 (slabL 4 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (83 : Fin 865)
      exact leaf_4_40_83
  have hchart := cSimp_eq_chiRep 4 (a := 40) rfl
    ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ] fl_4_40_728_426 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (-1/8) 1, slabPt (1/2) (-1/8) 1, slabPt (1/2) (-1/4) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_40_728_426) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (83 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_40_728_426)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨83⟩ : QbarCW.Cell) fl_4_40_728_426
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨728⟩ : QbarCell) < (⟨83⟩ : QbarCell) from lt_trans (show (⟨728⟩ : QbarCell) < (⟨426⟩ : QbarCell) from by decide) (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨426⟩ : QbarCell) < (⟨83⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨44, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (83 : Fin 865)) fl_4_40_728_426) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(840,203,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_840_203 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_840_203 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (840 : Fin 865)
      exact leaf_4_44_840
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (203 : Fin 865)
      exact leaf_4_44_203
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_840_203 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_840_203) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_840_203)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_840_203
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_203) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(857,203,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_857_203 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_857_203 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (857 : Fin 865)
      exact leaf_4_44_857
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (203 : Fin 865)
      exact leaf_4_44_203
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_857_203 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (1/2) (5/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_857_203) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_857_203)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_857_203
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨203⟩ : QbarCell) from by decide) (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨203⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_203) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(840,323,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_840_323 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_840_323 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (840 : Fin 865)
      exact leaf_4_44_840
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (323 : Fin 865)
      exact leaf_4_44_323
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_840_323 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (5/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_840_323) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_840_323)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_840_323
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨840⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨840⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_840_323) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(860,323,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_860_323 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_860_323 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (860 : Fin 865)
      exact leaf_4_44_860
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (323 : Fin 865)
      exact leaf_4_44_323
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_860_323 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (5/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_860_323) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_860_323)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_860_323
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨323⟩ : QbarCell) from by decide) (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨323⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_323) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(720,419,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_720_419 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_720_419 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (720 : Fin 865)
      exact leaf_4_44_720
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (419 : Fin 865)
      exact leaf_4_44_419
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_720_419 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_720_419) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_720_419)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_720_419
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_419) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(857,419,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_857_419 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_857_419 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (5/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (857 : Fin 865)
      exact leaf_4_44_857
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (419 : Fin 865)
      exact leaf_4_44_419
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_857_419 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (5/8) 1, slabPt (3/8) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_857_419) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_857_419)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_857_419
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨857⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨857⟩ : QbarCell) < (⟨419⟩ : QbarCell) from by decide) (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨419⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_857_419) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(720,427,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_720_427 :
    cChain 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_720_427 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (3/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (720 : Fin 865)
      exact leaf_4_44_720
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (427 : Fin 865)
      exact leaf_4_44_427
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_720_427 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (3/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_720_427) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_720_427)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_720_427
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨720⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨720⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_720_427) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(860,427,85)` of the square `44` of cusp `4`. -/
theorem ch_4_44_860_427 :
    cChain 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 44 := by
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
      (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 44 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 44 (slabL 4 (![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_4_44_860_427 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (5/8) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (860 : Fin 865)
      exact leaf_4_44_860
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (3/8) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (427 : Fin 865)
      exact leaf_4_44_427
    · show Work.RTOwed.kleinPt 44 (slabL 4 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (85 : Fin 865)
      exact leaf_4_44_85
  have hchart := cSimp_eq_chiRep 4 (a := 44) rfl
    ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ] fl_4_44_860_427 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 4 (slabV 4 ![ slabPt (5/8) (3/8) 1, slabPt (1/2) (3/8) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_4_44_860_427) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (85 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_4_44_860_427)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨85⟩ : QbarCW.Cell) fl_4_44_860_427
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨860⟩ : QbarCell) < (⟨85⟩ : QbarCell) from lt_trans (show (⟨860⟩ : QbarCell) < (⟨427⟩ : QbarCell) from by decide) (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨427⟩ : QbarCell) < (⟨85⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨42, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (85 : Fin 865)) fl_4_44_860_427) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
