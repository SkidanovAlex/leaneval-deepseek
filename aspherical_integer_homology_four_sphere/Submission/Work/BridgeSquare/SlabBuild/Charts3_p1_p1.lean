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



end

end Work.BridgeSquare.SlabBuild
