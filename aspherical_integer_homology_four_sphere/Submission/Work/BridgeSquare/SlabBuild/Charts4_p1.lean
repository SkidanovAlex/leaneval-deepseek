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
      (fun _ => show (⟨578⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide +kernel) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(593 < 302 < 103)` of `Q̄`. -/
def fl_4_16_593_302 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨593⟩ : QbarCell)) (⟨302⟩ : QbarCell)
      (fun _ => show (⟨593⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨302⟩ : QbarCell) from by decide +kernel) (show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨302⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(578 < 398 < 103)` of `Q̄`. -/
def fl_4_16_578_398 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨578⟩ : QbarCell)) (⟨398⟩ : QbarCell)
      (fun _ => show (⟨578⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨578⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨578⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide +kernel) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(596 < 398 < 103)` of `Q̄`. -/
def fl_4_16_596_398 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨596⟩ : QbarCell)) (⟨398⟩ : QbarCell)
      (fun _ => show (⟨596⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨398⟩ : QbarCell) from by decide +kernel) (show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨398⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(587 < 470 < 103)` of `Q̄`. -/
def fl_4_16_587_470 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨587⟩ : QbarCell)) (⟨470⟩ : QbarCell)
      (fun _ => show (⟨587⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide +kernel) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(593 < 470 < 103)` of `Q̄`. -/
def fl_4_16_593_470 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨593⟩ : QbarCell)) (⟨470⟩ : QbarCell)
      (fun _ => show (⟨593⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨593⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨593⟩ : QbarCell) < (⟨470⟩ : QbarCell) from by decide +kernel) (show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨470⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(587 < 478 < 103)` of `Q̄`. -/
def fl_4_16_587_478 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨587⟩ : QbarCell)) (⟨478⟩ : QbarCell)
      (fun _ => show (⟨587⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨587⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨587⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide +kernel) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(596 < 478 < 103)` of `Q̄`. -/
def fl_4_16_596_478 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨596⟩ : QbarCell)) (⟨478⟩ : QbarCell)
      (fun _ => show (⟨596⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide +kernel))
    (⟨103⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨596⟩ : QbarCell) < (⟨103⟩ : QbarCell) from lt_trans (show (⟨596⟩ : QbarCell) < (⟨478⟩ : QbarCell) from by decide +kernel) (show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨478⟩ : QbarCell) < (⟨103⟩ : QbarCell) from by decide +kernel)

/-- The flag `(734 < 270 < 105)` of `Q̄`. -/
def fl_4_17_734_270 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨734⟩ : QbarCell)) (⟨270⟩ : QbarCell)
      (fun _ => show (⟨734⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide +kernel) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(746 < 270 < 105)` of `Q̄`. -/
def fl_4_17_746_270 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨746⟩ : QbarCell)) (⟨270⟩ : QbarCell)
      (fun _ => show (⟨746⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨270⟩ : QbarCell) from by decide +kernel) (show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨270⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(734 < 374 < 105)` of `Q̄`. -/
def fl_4_17_734_374 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨734⟩ : QbarCell)) (⟨374⟩ : QbarCell)
      (fun _ => show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨734⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨734⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(749 < 374 < 105)` of `Q̄`. -/
def fl_4_17_749_374 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨749⟩ : QbarCell)) (⟨374⟩ : QbarCell)
      (fun _ => show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨374⟩ : QbarCell) from by decide +kernel) (show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨374⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(588 < 471 < 105)` of `Q̄`. -/
def fl_4_17_588_471 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨588⟩ : QbarCell)) (⟨471⟩ : QbarCell)
      (fun _ => show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(746 < 471 < 105)` of `Q̄`. -/
def fl_4_17_746_471 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨746⟩ : QbarCell)) (⟨471⟩ : QbarCell)
      (fun _ => show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨746⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨746⟩ : QbarCell) < (⟨471⟩ : QbarCell) from by decide +kernel) (show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨471⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(588 < 479 < 105)` of `Q̄`. -/
def fl_4_17_588_479 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨588⟩ : QbarCell)) (⟨479⟩ : QbarCell)
      (fun _ => show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨588⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨588⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(749 < 479 < 105)` of `Q̄`. -/
def fl_4_17_749_479 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨749⟩ : QbarCell)) (⟨479⟩ : QbarCell)
      (fun _ => show (⟨749⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel))
    (⟨105⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨749⟩ : QbarCell) < (⟨105⟩ : QbarCell) from lt_trans (show (⟨749⟩ : QbarCell) < (⟨479⟩ : QbarCell) from by decide +kernel) (show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨479⟩ : QbarCell) < (⟨105⟩ : QbarCell) from by decide +kernel)

/-- The flag `(623 < 298 < 89)` of `Q̄`. -/
def fl_4_18_623_298 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨623⟩ : QbarCell)) (⟨298⟩ : QbarCell)
      (fun _ => show (⟨623⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide +kernel) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(635 < 298 < 89)` of `Q̄`. -/
def fl_4_18_635_298 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨635⟩ : QbarCell)) (⟨298⟩ : QbarCell)
      (fun _ => show (⟨635⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨298⟩ : QbarCell) from by decide +kernel) (show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨298⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(623 < 350 < 89)` of `Q̄`. -/
def fl_4_18_623_350 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨623⟩ : QbarCell)) (⟨350⟩ : QbarCell)
      (fun _ => show (⟨623⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨623⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨623⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide +kernel) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(638 < 350 < 89)` of `Q̄`. -/
def fl_4_18_638_350 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨638⟩ : QbarCell)) (⟨350⟩ : QbarCell)
      (fun _ => show (⟨638⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨350⟩ : QbarCell) from by decide +kernel) (show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨350⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(629 < 438 < 89)` of `Q̄`. -/
def fl_4_18_629_438 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨629⟩ : QbarCell)) (⟨438⟩ : QbarCell)
      (fun _ => show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(635 < 438 < 89)` of `Q̄`. -/
def fl_4_18_635_438 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨635⟩ : QbarCell)) (⟨438⟩ : QbarCell)
      (fun _ => show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨635⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨635⟩ : QbarCell) < (⟨438⟩ : QbarCell) from by decide +kernel) (show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨438⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(629 < 446 < 89)` of `Q̄`. -/
def fl_4_18_629_446 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨629⟩ : QbarCell)) (⟨446⟩ : QbarCell)
      (fun _ => show (⟨629⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨629⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨629⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide +kernel) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(638 < 446 < 89)` of `Q̄`. -/
def fl_4_18_638_446 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨638⟩ : QbarCell)) (⟨446⟩ : QbarCell)
      (fun _ => show (⟨638⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide +kernel))
    (⟨89⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨638⟩ : QbarCell) < (⟨89⟩ : QbarCell) from lt_trans (show (⟨638⟩ : QbarCell) < (⟨446⟩ : QbarCell) from by decide +kernel) (show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨446⟩ : QbarCell) < (⟨89⟩ : QbarCell) from by decide +kernel)

/-- The flag `(662 < 238 < 96)` of `Q̄`. -/
def fl_4_20_662_238 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨662⟩ : QbarCell)) (⟨238⟩ : QbarCell)
      (fun _ => show (⟨662⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide +kernel) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(674 < 238 < 96)` of `Q̄`. -/
def fl_4_20_674_238 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨674⟩ : QbarCell)) (⟨238⟩ : QbarCell)
      (fun _ => show (⟨674⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨238⟩ : QbarCell) from by decide +kernel) (show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨238⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(662 < 394 < 96)` of `Q̄`. -/
def fl_4_20_662_394 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨662⟩ : QbarCell)) (⟨394⟩ : QbarCell)
      (fun _ => show (⟨662⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨662⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨662⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide +kernel) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(677 < 394 < 96)` of `Q̄`. -/
def fl_4_20_677_394 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨677⟩ : QbarCell)) (⟨394⟩ : QbarCell)
      (fun _ => show (⟨677⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨394⟩ : QbarCell) from by decide +kernel) (show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨394⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(668 < 454 < 96)` of `Q̄`. -/
def fl_4_20_668_454 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨668⟩ : QbarCell)) (⟨454⟩ : QbarCell)
      (fun _ => show (⟨668⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide +kernel) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(674 < 454 < 96)` of `Q̄`. -/
def fl_4_20_674_454 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨674⟩ : QbarCell)) (⟨454⟩ : QbarCell)
      (fun _ => show (⟨674⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨674⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨674⟩ : QbarCell) < (⟨454⟩ : QbarCell) from by decide +kernel) (show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨454⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(668 < 462 < 96)` of `Q̄`. -/
def fl_4_20_668_462 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨668⟩ : QbarCell)) (⟨462⟩ : QbarCell)
      (fun _ => show (⟨668⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨668⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨668⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide +kernel) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(677 < 462 < 96)` of `Q̄`. -/
def fl_4_20_677_462 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨677⟩ : QbarCell)) (⟨462⟩ : QbarCell)
      (fun _ => show (⟨677⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide +kernel))
    (⟨96⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨677⟩ : QbarCell) < (⟨96⟩ : QbarCell) from lt_trans (show (⟨677⟩ : QbarCell) < (⟨462⟩ : QbarCell) from by decide +kernel) (show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨462⟩ : QbarCell) < (⟨96⟩ : QbarCell) from by decide +kernel)

/-- The flag `(579 < 303 < 104)` of `Q̄`. -/
def fl_4_21_579_303 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨579⟩ : QbarCell)) (⟨303⟩ : QbarCell)
      (fun _ => show (⟨579⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide +kernel) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(614 < 303 < 104)` of `Q̄`. -/
def fl_4_21_614_303 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨614⟩ : QbarCell)) (⟨303⟩ : QbarCell)
      (fun _ => show (⟨614⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨303⟩ : QbarCell) from by decide +kernel) (show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨303⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(579 < 399 < 104)` of `Q̄`. -/
def fl_4_21_579_399 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨579⟩ : QbarCell)) (⟨399⟩ : QbarCell)
      (fun _ => show (⟨579⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨579⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨579⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide +kernel) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(617 < 399 < 104)` of `Q̄`. -/
def fl_4_21_617_399 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨617⟩ : QbarCell)) (⟨399⟩ : QbarCell)
      (fun _ => show (⟨617⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨399⟩ : QbarCell) from by decide +kernel) (show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨399⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(608 < 466 < 104)` of `Q̄`. -/
def fl_4_21_608_466 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨608⟩ : QbarCell)) (⟨466⟩ : QbarCell)
      (fun _ => show (⟨608⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide +kernel) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(614 < 466 < 104)` of `Q̄`. -/
def fl_4_21_614_466 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨614⟩ : QbarCell)) (⟨466⟩ : QbarCell)
      (fun _ => show (⟨614⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨614⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨614⟩ : QbarCell) < (⟨466⟩ : QbarCell) from by decide +kernel) (show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨466⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(608 < 474 < 104)` of `Q̄`. -/
def fl_4_21_608_474 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨608⟩ : QbarCell)) (⟨474⟩ : QbarCell)
      (fun _ => show (⟨608⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨608⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨608⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide +kernel) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(617 < 474 < 104)` of `Q̄`. -/
def fl_4_21_617_474 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨617⟩ : QbarCell)) (⟨474⟩ : QbarCell)
      (fun _ => show (⟨617⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide +kernel))
    (⟨104⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨617⟩ : QbarCell) < (⟨104⟩ : QbarCell) from lt_trans (show (⟨617⟩ : QbarCell) < (⟨474⟩ : QbarCell) from by decide +kernel) (show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨474⟩ : QbarCell) < (⟨104⟩ : QbarCell) from by decide +kernel)

/-- The flag `(773 < 266 < 91)` of `Q̄`. -/
def fl_4_22_773_266 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨773⟩ : QbarCell)) (⟨266⟩ : QbarCell)
      (fun _ => show (⟨773⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide +kernel) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(782 < 266 < 91)` of `Q̄`. -/
def fl_4_22_782_266 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨782⟩ : QbarCell)) (⟨266⟩ : QbarCell)
      (fun _ => show (⟨782⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨782⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨782⟩ : QbarCell) < (⟨266⟩ : QbarCell) from by decide +kernel) (show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨266⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(773 < 326 < 91)` of `Q̄`. -/
def fl_4_22_773_326 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨773⟩ : QbarCell)) (⟨326⟩ : QbarCell)
      (fun _ => show (⟨773⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨773⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨773⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide +kernel) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

/-- The flag `(785 < 326 < 91)` of `Q̄`. -/
def fl_4_22_785_326 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨785⟩ : QbarCell)) (⟨326⟩ : QbarCell)
      (fun _ => show (⟨785⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide +kernel))
    (⟨91⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨785⟩ : QbarCell) < (⟨91⟩ : QbarCell) from lt_trans (show (⟨785⟩ : QbarCell) < (⟨326⟩ : QbarCell) from by decide +kernel) (show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨326⟩ : QbarCell) < (⟨91⟩ : QbarCell) from by decide +kernel)

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


end

end Work.BridgeSquare.SlabBuild
