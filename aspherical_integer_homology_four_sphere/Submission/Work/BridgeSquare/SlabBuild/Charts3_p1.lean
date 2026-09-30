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

/-- The flag `(837 < 484 < 143)` of `Q̄`. -/
def fl_3_12_837_484 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨837⟩ : QbarCell)) (⟨484⟩ : QbarCell)
      (fun _ => show (⟨837⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨837⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨837⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel) (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(864 < 484 < 143)` of `Q̄`. -/
def fl_3_12_864_484 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨864⟩ : QbarCell)) (⟨484⟩ : QbarCell)
      (fun _ => show (⟨864⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨864⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨864⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel) (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(699 < 500 < 143)` of `Q̄`. -/
def fl_3_12_699_500 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨699⟩ : QbarCell)) (⟨500⟩ : QbarCell)
      (fun _ => show (⟨699⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨699⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨699⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel) (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(732 < 500 < 143)` of `Q̄`. -/
def fl_3_12_732_500 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨732⟩ : QbarCell)) (⟨500⟩ : QbarCell)
      (fun _ => show (⟨732⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨732⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨732⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel) (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(732 < 548 < 143)` of `Q̄`. -/
def fl_3_12_732_548 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨732⟩ : QbarCell)) (⟨548⟩ : QbarCell)
      (fun _ => show (⟨732⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨732⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨732⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel) (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(864 < 548 < 143)` of `Q̄`. -/
def fl_3_12_864_548 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨864⟩ : QbarCell)) (⟨548⟩ : QbarCell)
      (fun _ => show (⟨864⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨864⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨864⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel) (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(699 < 552 < 143)` of `Q̄`. -/
def fl_3_12_699_552 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨699⟩ : QbarCell)) (⟨552⟩ : QbarCell)
      (fun _ => show (⟨699⟩ : QbarCell) < (⟨552⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨699⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨699⟩ : QbarCell) < (⟨552⟩ : QbarCell) from by decide +kernel) (show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(837 < 552 < 143)` of `Q̄`. -/
def fl_3_12_837_552 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨837⟩ : QbarCell)) (⟨552⟩ : QbarCell)
      (fun _ => show (⟨837⟩ : QbarCell) < (⟨552⟩ : QbarCell) from by decide +kernel))
    (⟨143⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨837⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨837⟩ : QbarCell) < (⟨552⟩ : QbarCell) from by decide +kernel) (show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)

/-- The flag `(753 < 520 < 164)` of `Q̄`. -/
def fl_3_13_753_520 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨753⟩ : QbarCell)) (⟨520⟩ : QbarCell)
      (fun _ => show (⟨753⟩ : QbarCell) < (⟨520⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨753⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨753⟩ : QbarCell) < (⟨520⟩ : QbarCell) from by decide +kernel) (show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(789 < 520 < 164)` of `Q̄`. -/
def fl_3_13_789_520 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨789⟩ : QbarCell)) (⟨520⟩ : QbarCell)
      (fun _ => show (⟨789⟩ : QbarCell) < (⟨520⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨789⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨789⟩ : QbarCell) < (⟨520⟩ : QbarCell) from by decide +kernel) (show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(600 < 536 < 164)` of `Q̄`. -/
def fl_3_13_600_536 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨600⟩ : QbarCell)) (⟨536⟩ : QbarCell)
      (fun _ => show (⟨600⟩ : QbarCell) < (⟨536⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨600⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨600⟩ : QbarCell) < (⟨536⟩ : QbarCell) from by decide +kernel) (show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(642 < 536 < 164)` of `Q̄`. -/
def fl_3_13_642_536 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨642⟩ : QbarCell)) (⟨536⟩ : QbarCell)
      (fun _ => show (⟨642⟩ : QbarCell) < (⟨536⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨642⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨642⟩ : QbarCell) < (⟨536⟩ : QbarCell) from by decide +kernel) (show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(642 < 572 < 164)` of `Q̄`. -/
def fl_3_13_642_572 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨642⟩ : QbarCell)) (⟨572⟩ : QbarCell)
      (fun _ => show (⟨642⟩ : QbarCell) < (⟨572⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨642⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨642⟩ : QbarCell) < (⟨572⟩ : QbarCell) from by decide +kernel) (show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(789 < 572 < 164)` of `Q̄`. -/
def fl_3_13_789_572 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨789⟩ : QbarCell)) (⟨572⟩ : QbarCell)
      (fun _ => show (⟨789⟩ : QbarCell) < (⟨572⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨789⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨789⟩ : QbarCell) < (⟨572⟩ : QbarCell) from by decide +kernel) (show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨572⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(600 < 576 < 164)` of `Q̄`. -/
def fl_3_13_600_576 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨600⟩ : QbarCell)) (⟨576⟩ : QbarCell)
      (fun _ => show (⟨600⟩ : QbarCell) < (⟨576⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨600⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨600⟩ : QbarCell) < (⟨576⟩ : QbarCell) from by decide +kernel) (show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(753 < 576 < 164)` of `Q̄`. -/
def fl_3_13_753_576 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨753⟩ : QbarCell)) (⟨576⟩ : QbarCell)
      (fun _ => show (⟨753⟩ : QbarCell) < (⟨576⟩ : QbarCell) from by decide +kernel))
    (⟨164⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨753⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨753⟩ : QbarCell) < (⟨576⟩ : QbarCell) from by decide +kernel) (show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨576⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)

/-- The flag `(822 < 516 < 157)` of `Q̄`. -/
def fl_3_14_822_516 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨822⟩ : QbarCell)) (⟨516⟩ : QbarCell)
      (fun _ => show (⟨822⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨822⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨822⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel) (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(852 < 516 < 157)` of `Q̄`. -/
def fl_3_14_852_516 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨852⟩ : QbarCell)) (⟨516⟩ : QbarCell)
      (fun _ => show (⟨852⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨852⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨852⟩ : QbarCell) < (⟨516⟩ : QbarCell) from by decide +kernel) (show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨516⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(681 < 532 < 157)` of `Q̄`. -/
def fl_3_14_681_532 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨681⟩ : QbarCell)) (⟨532⟩ : QbarCell)
      (fun _ => show (⟨681⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨681⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨681⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel) (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(717 < 532 < 157)` of `Q̄`. -/
def fl_3_14_717_532 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨717⟩ : QbarCell)) (⟨532⟩ : QbarCell)
      (fun _ => show (⟨717⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨717⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨717⟩ : QbarCell) < (⟨532⟩ : QbarCell) from by decide +kernel) (show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨532⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(717 < 564 < 157)` of `Q̄`. -/
def fl_3_14_717_564 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨717⟩ : QbarCell)) (⟨564⟩ : QbarCell)
      (fun _ => show (⟨717⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨717⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨717⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel) (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(852 < 564 < 157)` of `Q̄`. -/
def fl_3_14_852_564 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨852⟩ : QbarCell)) (⟨564⟩ : QbarCell)
      (fun _ => show (⟨852⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨852⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨852⟩ : QbarCell) < (⟨564⟩ : QbarCell) from by decide +kernel) (show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨564⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(681 < 568 < 157)` of `Q̄`. -/
def fl_3_14_681_568 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨681⟩ : QbarCell)) (⟨568⟩ : QbarCell)
      (fun _ => show (⟨681⟩ : QbarCell) < (⟨568⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨681⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨681⟩ : QbarCell) < (⟨568⟩ : QbarCell) from by decide +kernel) (show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(822 < 568 < 157)` of `Q̄`. -/
def fl_3_14_822_568 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨822⟩ : QbarCell)) (⟨568⟩ : QbarCell)
      (fun _ => show (⟨822⟩ : QbarCell) < (⟨568⟩ : QbarCell) from by decide +kernel))
    (⟨157⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨822⟩ : QbarCell) < (⟨157⟩ : QbarCell) from lt_trans (show (⟨822⟩ : QbarCell) < (⟨568⟩ : QbarCell) from by decide +kernel) (show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨568⟩ : QbarCell) < (⟨157⟩ : QbarCell) from by decide +kernel)

/-- The flag `(771 < 488 < 150)` of `Q̄`. -/
def fl_3_15_771_488 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨771⟩ : QbarCell)) (⟨488⟩ : QbarCell)
      (fun _ => show (⟨771⟩ : QbarCell) < (⟨488⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨771⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨771⟩ : QbarCell) < (⟨488⟩ : QbarCell) from by decide +kernel) (show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(804 < 488 < 150)` of `Q̄`. -/
def fl_3_15_804_488 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨804⟩ : QbarCell)) (⟨488⟩ : QbarCell)
      (fun _ => show (⟨804⟩ : QbarCell) < (⟨488⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨804⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨804⟩ : QbarCell) < (⟨488⟩ : QbarCell) from by decide +kernel) (show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨488⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(621 < 504 < 150)` of `Q̄`. -/
def fl_3_15_621_504 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨621⟩ : QbarCell)) (⟨504⟩ : QbarCell)
      (fun _ => show (⟨621⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨621⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨621⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel) (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(660 < 504 < 150)` of `Q̄`. -/
def fl_3_15_660_504 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨660⟩ : QbarCell)) (⟨504⟩ : QbarCell)
      (fun _ => show (⟨660⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨660⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨660⟩ : QbarCell) < (⟨504⟩ : QbarCell) from by decide +kernel) (show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨504⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(660 < 556 < 150)` of `Q̄`. -/
def fl_3_15_660_556 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨660⟩ : QbarCell)) (⟨556⟩ : QbarCell)
      (fun _ => show (⟨660⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨660⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨660⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel) (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(804 < 556 < 150)` of `Q̄`. -/
def fl_3_15_804_556 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨804⟩ : QbarCell)) (⟨556⟩ : QbarCell)
      (fun _ => show (⟨804⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨804⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨804⟩ : QbarCell) < (⟨556⟩ : QbarCell) from by decide +kernel) (show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨556⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(621 < 560 < 150)` of `Q̄`. -/
def fl_3_15_621_560 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨621⟩ : QbarCell)) (⟨560⟩ : QbarCell)
      (fun _ => show (⟨621⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨621⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨621⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel) (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-- The flag `(771 < 560 < 150)` of `Q̄`. -/
def fl_3_15_771_560 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨771⟩ : QbarCell)) (⟨560⟩ : QbarCell)
      (fun _ => show (⟨771⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel))
    (⟨150⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨771⟩ : QbarCell) < (⟨150⟩ : QbarCell) from lt_trans (show (⟨771⟩ : QbarCell) < (⟨560⟩ : QbarCell) from by decide +kernel) (show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨560⟩ : QbarCell) < (⟨150⟩ : QbarCell) from by decide +kernel)

/-! ## The leaf points of the wall squares -/

/-- Leaf `143` of the square `12` of cusp `3`. -/
theorem leaf_3_12_143 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (143 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `484` of the square `12` of cusp `3`. -/
theorem leaf_3_12_484 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (484 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `500` of the square `12` of cusp `3`. -/
theorem leaf_3_12_500 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (500 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `548` of the square `12` of cusp `3`. -/
theorem leaf_3_12_548 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (548 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `552` of the square `12` of cusp `3`. -/
theorem leaf_3_12_552 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (552 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `699` of the square `12` of cusp `3`. -/
theorem leaf_3_12_699 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (699 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `732` of the square `12` of cusp `3`. -/
theorem leaf_3_12_732 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (732 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `837` of the square `12` of cusp `3`. -/
theorem leaf_3_12_837 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (837 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `864` of the square `12` of cusp `3`. -/
theorem leaf_3_12_864 :
    Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (864 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `164` of the square `13` of cusp `3`. -/
theorem leaf_3_13_164 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (164 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `520` of the square `13` of cusp `3`. -/
theorem leaf_3_13_520 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (520 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `536` of the square `13` of cusp `3`. -/
theorem leaf_3_13_536 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (536 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `572` of the square `13` of cusp `3`. -/
theorem leaf_3_13_572 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (572 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `576` of the square `13` of cusp `3`. -/
theorem leaf_3_13_576 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (576 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `600` of the square `13` of cusp `3`. -/
theorem leaf_3_13_600 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (600 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `642` of the square `13` of cusp `3`. -/
theorem leaf_3_13_642 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (642 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `753` of the square `13` of cusp `3`. -/
theorem leaf_3_13_753 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (753 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `789` of the square `13` of cusp `3`. -/
theorem leaf_3_13_789 :
    Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (789 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `157` of the square `14` of cusp `3`. -/
theorem leaf_3_14_157 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (157 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `516` of the square `14` of cusp `3`. -/
theorem leaf_3_14_516 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (516 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `532` of the square `14` of cusp `3`. -/
theorem leaf_3_14_532 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (532 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `564` of the square `14` of cusp `3`. -/
theorem leaf_3_14_564 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (564 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `568` of the square `14` of cusp `3`. -/
theorem leaf_3_14_568 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (568 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `681` of the square `14` of cusp `3`. -/
theorem leaf_3_14_681 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (681 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `717` of the square `14` of cusp `3`. -/
theorem leaf_3_14_717 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (717 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `822` of the square `14` of cusp `3`. -/
theorem leaf_3_14_822 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (822 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `852` of the square `14` of cusp `3`. -/
theorem leaf_3_14_852 :
    Work.RTOwed.kleinPt 14 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (852 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `150` of the square `15` of cusp `3`. -/
theorem leaf_3_15_150 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (150 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `488` of the square `15` of cusp `3`. -/
theorem leaf_3_15_488 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (488 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `504` of the square `15` of cusp `3`. -/
theorem leaf_3_15_504 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (504 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `556` of the square `15` of cusp `3`. -/
theorem leaf_3_15_556 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (556 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `560` of the square `15` of cusp `3`. -/
theorem leaf_3_15_560 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (560 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `621` of the square `15` of cusp `3`. -/
theorem leaf_3_15_621 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (621 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `660` of the square `15` of cusp `3`. -/
theorem leaf_3_15_660 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (660 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `771` of the square `15` of cusp `3`. -/
theorem leaf_3_15_771 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-3/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (771 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `804` of the square `15` of cusp `3`. -/
theorem leaf_3_15_804 :
    Work.RTOwed.kleinPt 15 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (804 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- The chart identity of the flag `(837,484,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_837_484 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_837_484 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (837 : Fin 865)
      exact leaf_3_12_837
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (484 : Fin 865)
      exact leaf_3_12_484
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_3_12_837_484 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_837_484) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_837_484)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_837_484
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨837⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨837⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel) (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_484) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(864,484,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_864_484 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_864_484 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (864 : Fin 865)
      exact leaf_3_12_864
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (484 : Fin 865)
      exact leaf_3_12_484
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_3_12_864_484 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_864_484) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_864_484)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_864_484
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨864⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨864⟩ : QbarCell) < (⟨484⟩ : QbarCell) from by decide +kernel) (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨484⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_484) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(699,500,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_699_500 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_699_500 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (699 : Fin 865)
      exact leaf_3_12_699
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (500 : Fin 865)
      exact leaf_3_12_500
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_3_12_699_500 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_699_500) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_699_500)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_699_500
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨699⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨699⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel) (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_500) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(732,500,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_732_500 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_732_500 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (732 : Fin 865)
      exact leaf_3_12_732
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (500 : Fin 865)
      exact leaf_3_12_500
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_3_12_732_500 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_732_500) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_732_500)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_732_500
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨732⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨732⟩ : QbarCell) < (⟨500⟩ : QbarCell) from by decide +kernel) (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨500⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_500) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(732,548,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_732_548 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_732_548 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (732 : Fin 865)
      exact leaf_3_12_732
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (548 : Fin 865)
      exact leaf_3_12_548
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_3_12_732_548 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_732_548) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_732_548)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_732_548
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨732⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨732⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel) (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_732_548) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(864,548,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_864_548 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_548))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_864_548 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (864 : Fin 865)
      exact leaf_3_12_864
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (548 : Fin 865)
      exact leaf_3_12_548
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_3_12_864_548 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_864_548) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_864_548)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_548) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_864_548
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨864⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨864⟩ : QbarCell) < (⟨548⟩ : QbarCell) from by decide +kernel) (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨548⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_548))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_548) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_864_548) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(699,552,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_699_552 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_552))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_699_552 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (699 : Fin 865)
      exact leaf_3_12_699
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (552 : Fin 865)
      exact leaf_3_12_552
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_3_12_699_552 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_699_552) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_699_552)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_552) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_699_552
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨699⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨699⟩ : QbarCell) < (⟨552⟩ : QbarCell) from by decide +kernel) (show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_552))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_552) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_699_552) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(837,552,143)` of the square `12` of cusp `3`. -/
theorem ch_3_12_837_552 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_552))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 12 := by
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
      (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 12 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 12 (slabL 3 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_12_837_552 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (837 : Fin 865)
      exact leaf_3_12_837
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (552 : Fin 865)
      exact leaf_3_12_552
    · show Work.RTOwed.kleinPt 12 (slabL 3 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (143 : Fin 865)
      exact leaf_3_12_143
  have hchart := cSimp_eq_chiRep 3 (a := 12) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_3_12_837_552 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_3_12_837_552) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (143 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_3_12_837_552)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_552) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨143⟩ : QbarCW.Cell) fl_3_12_837_552
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨837⟩ : QbarCell) < (⟨143⟩ : QbarCell) from lt_trans (show (⟨837⟩ : QbarCell) < (⟨552⟩ : QbarCell) from by decide +kernel) (show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨552⟩ : QbarCell) < (⟨143⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_552))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_552) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨165, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (143 : Fin 865)) fl_3_12_837_552) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(753,520,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_753_520 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_520))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_753_520 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (753 : Fin 865)
      exact leaf_3_13_753
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (520 : Fin 865)
      exact leaf_3_13_520
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_3_13_753_520 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_753_520) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_753_520)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_520) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_753_520
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨753⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨753⟩ : QbarCell) < (⟨520⟩ : QbarCell) from by decide +kernel) (show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_520))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_520) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_753_520) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(789,520,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_789_520 :
    cChain 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_520))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_789_520 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (789 : Fin 865)
      exact leaf_3_13_789
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (520 : Fin 865)
      exact leaf_3_13_520
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_3_13_789_520 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_789_520) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_789_520)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_520) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_789_520
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨789⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨789⟩ : QbarCell) < (⟨520⟩ : QbarCell) from by decide +kernel) (show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨520⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_520))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_520) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_789_520) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(600,536,164)` of the square `13` of cusp `3`. -/
theorem ch_3_13_600_536 :
    cChain 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_536))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 13 := by
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
      (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 13 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 13 (slabL 3 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_3_13_600_536 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (600 : Fin 865)
      exact leaf_3_13_600
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (536 : Fin 865)
      exact leaf_3_13_536
    · show Work.RTOwed.kleinPt 13 (slabL 3 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (164 : Fin 865)
      exact leaf_3_13_164
  have hchart := cSimp_eq_chiRep 3 (a := 13) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_3_13_600_536 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 3 (slabV 3 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_3_13_600_536) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (164 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide +kernel
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_3_13_600_536)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_536) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨164⟩ : QbarCW.Cell) fl_3_13_600_536
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨600⟩ : QbarCell) < (⟨164⟩ : QbarCell) from lt_trans (show (⟨600⟩ : QbarCell) < (⟨536⟩ : QbarCell) from by decide +kernel) (show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel))
        · exact le_of_lt (show (⟨536⟩ : QbarCell) < (⟨164⟩ : QbarCell) from by decide +kernel)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_536))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_536) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨83, by decide +kernel⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (164 : Fin 865)) fl_3_13_600_536) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w


end

end Work.BridgeSquare.SlabBuild
