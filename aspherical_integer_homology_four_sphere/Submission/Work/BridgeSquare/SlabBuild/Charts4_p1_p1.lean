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



end

end Work.BridgeSquare.SlabBuild
