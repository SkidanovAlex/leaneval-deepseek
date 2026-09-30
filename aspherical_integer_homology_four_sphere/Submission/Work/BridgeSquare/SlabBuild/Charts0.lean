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

/-- The flag `(843 < 196 < 58)` of `Q̄`. -/
def fl_0_0_843_196 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨843⟩ : QbarCell)) (⟨196⟩ : QbarCell)
      (fun _ => show (⟨843⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨843⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨843⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide) (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(855 < 196 < 58)` of `Q̄`. -/
def fl_0_0_855_196 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨855⟩ : QbarCell)) (⟨196⟩ : QbarCell)
      (fun _ => show (⟨855⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨855⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨855⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide) (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(780 < 260 < 58)` of `Q̄`. -/
def fl_0_0_780_260 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨780⟩ : QbarCell)) (⟨260⟩ : QbarCell)
      (fun _ => show (⟨780⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨780⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨780⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide) (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(795 < 260 < 58)` of `Q̄`. -/
def fl_0_0_795_260 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨795⟩ : QbarCell)) (⟨260⟩ : QbarCell)
      (fun _ => show (⟨795⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨795⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨795⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide) (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(795 < 332 < 58)` of `Q̄`. -/
def fl_0_0_795_332 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨795⟩ : QbarCell)) (⟨332⟩ : QbarCell)
      (fun _ => show (⟨795⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨795⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨795⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide) (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(855 < 332 < 58)` of `Q̄`. -/
def fl_0_0_855_332 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨855⟩ : QbarCell)) (⟨332⟩ : QbarCell)
      (fun _ => show (⟨855⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨855⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨855⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide) (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(780 < 336 < 58)` of `Q̄`. -/
def fl_0_0_780_336 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨780⟩ : QbarCell)) (⟨336⟩ : QbarCell)
      (fun _ => show (⟨780⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨780⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨780⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide) (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(843 < 336 < 58)` of `Q̄`. -/
def fl_0_0_843_336 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨843⟩ : QbarCell)) (⟨336⟩ : QbarCell)
      (fun _ => show (⟨843⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨843⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨843⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide) (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
      · exact show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)

/-- The flag `(708 < 228 < 65)` of `Q̄`. -/
def fl_0_1_708_228 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨708⟩ : QbarCell)) (⟨228⟩ : QbarCell)
      (fun _ => show (⟨708⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide) (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(723 < 228 < 65)` of `Q̄`. -/
def fl_0_1_723_228 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨723⟩ : QbarCell)) (⟨228⟩ : QbarCell)
      (fun _ => show (⟨723⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide) (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(633 < 292 < 65)` of `Q̄`. -/
def fl_0_1_633_292 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨633⟩ : QbarCell)) (⟨292⟩ : QbarCell)
      (fun _ => show (⟨633⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(651 < 292 < 65)` of `Q̄`. -/
def fl_0_1_651_292 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨651⟩ : QbarCell)) (⟨292⟩ : QbarCell)
      (fun _ => show (⟨651⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(651 < 356 < 65)` of `Q̄`. -/
def fl_0_1_651_356 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨651⟩ : QbarCell)) (⟨356⟩ : QbarCell)
      (fun _ => show (⟨651⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(723 < 356 < 65)` of `Q̄`. -/
def fl_0_1_723_356 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨723⟩ : QbarCell)) (⟨356⟩ : QbarCell)
      (fun _ => show (⟨723⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(633 < 360 < 65)` of `Q̄`. -/
def fl_0_1_633_360 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨633⟩ : QbarCell)) (⟨360⟩ : QbarCell)
      (fun _ => show (⟨633⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(708 < 360 < 65)` of `Q̄`. -/
def fl_0_1_708_360 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨708⟩ : QbarCell)) (⟨360⟩ : QbarCell)
      (fun _ => show (⟨708⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
      · exact show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)

/-- The flag `(672 < 232 < 79)` of `Q̄`. -/
def fl_0_2_672_232 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨672⟩ : QbarCell)) (⟨232⟩ : QbarCell)
      (fun _ => show (⟨672⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(690 < 232 < 79)` of `Q̄`. -/
def fl_0_2_690_232 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨690⟩ : QbarCell)) (⟨232⟩ : QbarCell)
      (fun _ => show (⟨690⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(591 < 296 < 79)` of `Q̄`. -/
def fl_0_2_591_296 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨591⟩ : QbarCell)) (⟨296⟩ : QbarCell)
      (fun _ => show (⟨591⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(612 < 296 < 79)` of `Q̄`. -/
def fl_0_2_612_296 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨612⟩ : QbarCell)) (⟨296⟩ : QbarCell)
      (fun _ => show (⟨612⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(612 < 404 < 79)` of `Q̄`. -/
def fl_0_2_612_404 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨612⟩ : QbarCell)) (⟨404⟩ : QbarCell)
      (fun _ => show (⟨612⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(690 < 404 < 79)` of `Q̄`. -/
def fl_0_2_690_404 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨690⟩ : QbarCell)) (⟨404⟩ : QbarCell)
      (fun _ => show (⟨690⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(591 < 408 < 79)` of `Q̄`. -/
def fl_0_2_591_408 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨591⟩ : QbarCell)) (⟨408⟩ : QbarCell)
      (fun _ => show (⟨591⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(672 < 408 < 79)` of `Q̄`. -/
def fl_0_2_672_408 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨672⟩ : QbarCell)) (⟨408⟩ : QbarCell)
      (fun _ => show (⟨672⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
      · exact show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)

/-- The flag `(813 < 200 < 72)` of `Q̄`. -/
def fl_0_3_813_200 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨813⟩ : QbarCell)) (⟨200⟩ : QbarCell)
      (fun _ => show (⟨813⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(828 < 200 < 72)` of `Q̄`. -/
def fl_0_3_828_200 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨828⟩ : QbarCell)) (⟨200⟩ : QbarCell)
      (fun _ => show (⟨828⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(744 < 264 < 72)` of `Q̄`. -/
def fl_0_3_744_264 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨744⟩ : QbarCell)) (⟨264⟩ : QbarCell)
      (fun _ => show (⟨744⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(762 < 264 < 72)` of `Q̄`. -/
def fl_0_3_762_264 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨762⟩ : QbarCell)) (⟨264⟩ : QbarCell)
      (fun _ => show (⟨762⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(762 < 380 < 72)` of `Q̄`. -/
def fl_0_3_762_380 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨762⟩ : QbarCell)) (⟨380⟩ : QbarCell)
      (fun _ => show (⟨762⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(828 < 380 < 72)` of `Q̄`. -/
def fl_0_3_828_380 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨828⟩ : QbarCell)) (⟨380⟩ : QbarCell)
      (fun _ => show (⟨828⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(744 < 384 < 72)` of `Q̄`. -/
def fl_0_3_744_384 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨744⟩ : QbarCell)) (⟨384⟩ : QbarCell)
      (fun _ => show (⟨744⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-- The flag `(813 < 384 < 72)` of `Q̄`. -/
def fl_0_3_813_384 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨813⟩ : QbarCell)) (⟨384⟩ : QbarCell)
      (fun _ => show (⟨813⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
      · exact show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)

/-! ## The leaf points of the wall squares -/

/-- Leaf `58` of the square `0` of cusp `0`. -/
theorem leaf_0_0_58 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (58 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `196` of the square `0` of cusp `0`. -/
theorem leaf_0_0_196 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (196 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `260` of the square `0` of cusp `0`. -/
theorem leaf_0_0_260 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (260 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `332` of the square `0` of cusp `0`. -/
theorem leaf_0_0_332 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (332 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `336` of the square `0` of cusp `0`. -/
theorem leaf_0_0_336 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (336 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `780` of the square `0` of cusp `0`. -/
theorem leaf_0_0_780 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (780 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `795` of the square `0` of cusp `0`. -/
theorem leaf_0_0_795 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (795 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `843` of the square `0` of cusp `0`. -/
theorem leaf_0_0_843 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (843 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `855` of the square `0` of cusp `0`. -/
theorem leaf_0_0_855 :
    Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (855 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `65` of the square `1` of cusp `0`. -/
theorem leaf_0_1_65 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (65 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `228` of the square `1` of cusp `0`. -/
theorem leaf_0_1_228 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (228 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `292` of the square `1` of cusp `0`. -/
theorem leaf_0_1_292 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (292 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `356` of the square `1` of cusp `0`. -/
theorem leaf_0_1_356 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (356 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `360` of the square `1` of cusp `0`. -/
theorem leaf_0_1_360 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (360 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `633` of the square `1` of cusp `0`. -/
theorem leaf_0_1_633 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (633 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `651` of the square `1` of cusp `0`. -/
theorem leaf_0_1_651 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (651 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `708` of the square `1` of cusp `0`. -/
theorem leaf_0_1_708 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (708 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `723` of the square `1` of cusp `0`. -/
theorem leaf_0_1_723 :
    Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (723 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `79` of the square `2` of cusp `0`. -/
theorem leaf_0_2_79 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (79 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `232` of the square `2` of cusp `0`. -/
theorem leaf_0_2_232 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (232 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `296` of the square `2` of cusp `0`. -/
theorem leaf_0_2_296 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (296 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `404` of the square `2` of cusp `0`. -/
theorem leaf_0_2_404 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (404 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `408` of the square `2` of cusp `0`. -/
theorem leaf_0_2_408 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (408 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `591` of the square `2` of cusp `0`. -/
theorem leaf_0_2_591 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (591 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `612` of the square `2` of cusp `0`. -/
theorem leaf_0_2_612 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (612 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `672` of the square `2` of cusp `0`. -/
theorem leaf_0_2_672 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (672 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `690` of the square `2` of cusp `0`. -/
theorem leaf_0_2_690 :
    Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (690 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `72` of the square `3` of cusp `0`. -/
theorem leaf_0_3_72 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (72 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `200` of the square `3` of cusp `0`. -/
theorem leaf_0_3_200 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (200 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `264` of the square `3` of cusp `0`. -/
theorem leaf_0_3_264 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (264 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `380` of the square `3` of cusp `0`. -/
theorem leaf_0_3_380 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (380 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `384` of the square `3` of cusp `0`. -/
theorem leaf_0_3_384 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (384 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `744` of the square `3` of cusp `0`. -/
theorem leaf_0_3_744 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (744 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `762` of the square `3` of cusp `0`. -/
theorem leaf_0_3_762 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (762 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `813` of the square `3` of cusp `0`. -/
theorem leaf_0_3_813 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (813 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- Leaf `828` of the square `3` of cusp `0`. -/
theorem leaf_0_3_828 :
    Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
      = QbarPD.posR (828 : Fin 865) := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp only [QbarPD, Work.ConvexCells.PolytopeData.posR, Work.ConvexCells.toE,
      Work.RTOwed.kleinPt, Work.Cusp.cubeXToKlein, Work.Cusp.cubeXToKleinb,
      Work.MbarHomology.qPos, slabL, slabPt, Work.Cusp.lam2, Work.Cusp.lam3,
      Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.latMod, Work.RTOwed.cuspH,
      Work.BridgeSquare.cuspHm, dirKappa, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.head_val', Matrix.tail_val', Fin.isValue,
      Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

/-- The chart identity of the flag `(843,196,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_843_196 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_843_196 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (843 : Fin 865)
      exact leaf_0_0_843
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (196 : Fin 865)
      exact leaf_0_0_196
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_0_0_843_196 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_843_196) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_843_196)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_843_196
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨843⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨843⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide) (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_196) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(855,196,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_855_196 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_855_196 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (855 : Fin 865)
      exact leaf_0_0_855
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (196 : Fin 865)
      exact leaf_0_0_196
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ] fl_0_0_855_196 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_855_196) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_855_196)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_855_196
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨855⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨855⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide) (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_196) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(780,260,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_780_260 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_780_260 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (780 : Fin 865)
      exact leaf_0_0_780
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (260 : Fin 865)
      exact leaf_0_0_260
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_0_0_780_260 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_780_260) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_780_260)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_780_260
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨780⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨780⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide) (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_260) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(795,260,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_795_260 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_795_260 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (795 : Fin 865)
      exact leaf_0_0_795
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (260 : Fin 865)
      exact leaf_0_0_260
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ] fl_0_0_795_260 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (0) (-1/4) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_795_260) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_795_260)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_795_260
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨795⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨795⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide) (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_260) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(795,332,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_795_332 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_795_332 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (795 : Fin 865)
      exact leaf_0_0_795
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (332 : Fin 865)
      exact leaf_0_0_332
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_0_0_795_332 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_795_332) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_795_332)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_795_332
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨795⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨795⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide) (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_795_332) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(855,332,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_855_332 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_855_332 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (855 : Fin 865)
      exact leaf_0_0_855
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (332 : Fin 865)
      exact leaf_0_0_332
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ] fl_0_0_855_332 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_855_332) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_855_332)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_855_332
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨855⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨855⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide) (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_855_332) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(780,336,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_780_336 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_780_336 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (780 : Fin 865)
      exact leaf_0_0_780
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (336 : Fin 865)
      exact leaf_0_0_336
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_0_0_780_336 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (-1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_780_336) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_780_336)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_780_336
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨780⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨780⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide) (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_780_336) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(843,336,58)` of the square `0` of cusp `0`. -/
theorem ch_0_0_843_336 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 0 := by
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
      (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 0 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 0 (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_0_843_336 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (843 : Fin 865)
      exact leaf_0_0_843
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (-1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (336 : Fin 865)
      exact leaf_0_0_336
    · show Work.RTOwed.kleinPt 0 (slabL 0 (slabPt (0) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (58 : Fin 865)
      exact leaf_0_0_58
  have hchart := cSimp_eq_chiRep 0 (a := 0) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ] fl_0_0_843_336 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (0) 1, slabPt (0) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_0_843_336) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (58 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_0_843_336)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨58⟩ : QbarCW.Cell) fl_0_0_843_336
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨843⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨843⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide) (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨152, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (58 : Fin 865)) fl_0_0_843_336) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(708,228,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_708_228 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_228))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_708_228 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (708 : Fin 865)
      exact leaf_0_1_708
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (228 : Fin 865)
      exact leaf_0_1_228
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_0_1_708_228 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_708_228) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_708_228)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_228) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_708_228
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide) (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_228))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_228) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_228) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(723,228,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_723_228 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_228))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_723_228 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (723 : Fin 865)
      exact leaf_0_1_723
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (228 : Fin 865)
      exact leaf_0_1_228
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ] fl_0_1_723_228 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (0) (1/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_723_228) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_723_228)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_228) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_723_228
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide) (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_228))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_228) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_228) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(633,292,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_633_292 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_292))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_633_292 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (633 : Fin 865)
      exact leaf_0_1_633
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (292 : Fin 865)
      exact leaf_0_1_292
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_0_1_633_292 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_633_292) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_633_292)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_292) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_633_292
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_292))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_292) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_292) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(651,292,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_651_292 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_651_292 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (651 : Fin 865)
      exact leaf_0_1_651
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (292 : Fin 865)
      exact leaf_0_1_292
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ] fl_0_1_651_292 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (0) (3/4) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_651_292) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_651_292)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_651_292
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_292) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(651,356,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_651_356 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_651_356 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (651 : Fin 865)
      exact leaf_0_1_651
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (356 : Fin 865)
      exact leaf_0_1_356
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_651_356 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_651_356) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_651_356)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_651_356
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_651_356) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(723,356,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_723_356 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_723_356 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (723 : Fin 865)
      exact leaf_0_1_723
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (356 : Fin 865)
      exact leaf_0_1_356
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_723_356 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_723_356) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_723_356)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_723_356
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_723_356) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(633,360,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_633_360 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_633_360 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (633 : Fin 865)
      exact leaf_0_1_633
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (360 : Fin 865)
      exact leaf_0_1_360
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_633_360 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (3/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_633_360) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_633_360)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_633_360
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_633_360) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(708,360,65)` of the square `1` of cusp `0`. -/
theorem ch_0_1_708_360 :
    cChain 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 1 := by
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
      (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 1 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 1 (slabL 0 (![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_1_708_360 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (708 : Fin 865)
      exact leaf_0_1_708
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (-1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (360 : Fin 865)
      exact leaf_0_1_360
    · show Work.RTOwed.kleinPt 1 (slabL 0 (slabPt (0) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (65 : Fin 865)
      exact leaf_0_1_65
  have hchart := cSimp_eq_chiRep 0 (a := 1) rfl
    ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ] fl_0_1_708_360 (1 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (-1/4) (1/4) 1, slabPt (-1/4) (1/2) 1, slabPt (0) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((1 : ZMod 2), fl_0_1_708_360) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (1 : ZMod 2) (65 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((1 : ZMod 2), fl_0_1_708_360)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360) := by
    have h := Mbar.flagRel_act_facet (1 : ZMod 2) 2 (⟨65⟩ : QbarCW.Cell) fl_0_1_708_360
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨158, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (1 : ZMod 2) (65 : Fin 865)) fl_0_1_708_360) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(672,232,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_672_232 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_672_232 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (672 : Fin 865)
      exact leaf_0_2_672
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (232 : Fin 865)
      exact leaf_0_2_232
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_672_232 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_672_232) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_672_232)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_672_232
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_232) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(690,232,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_690_232 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_690_232 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (690 : Fin 865)
      exact leaf_0_2_690
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (232 : Fin 865)
      exact leaf_0_2_232
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_690_232 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (1/2) (-1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_690_232) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_690_232)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_690_232
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_232) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(591,296,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_591_296 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_591_296 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (591 : Fin 865)
      exact leaf_0_2_591
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (296 : Fin 865)
      exact leaf_0_2_296
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_591_296 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_591_296) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_591_296)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_591_296
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_296) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(612,296,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_612_296 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_612_296 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (612 : Fin 865)
      exact leaf_0_2_612
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (296 : Fin 865)
      exact leaf_0_2_296
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ] fl_0_2_612_296 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_612_296) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_612_296)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_612_296
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_296) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(612,404,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_612_404 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_612_404 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (612 : Fin 865)
      exact leaf_0_2_612
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (404 : Fin 865)
      exact leaf_0_2_404
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_612_404 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_612_404) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_612_404)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_612_404
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_612_404) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(690,404,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_690_404 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_690_404 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (690 : Fin 865)
      exact leaf_0_2_690
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (3/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (404 : Fin 865)
      exact leaf_0_2_404
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_690_404 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (-1/4) 1, slabPt (3/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_690_404) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_690_404)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_690_404
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_690_404) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(591,408,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_591_408 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_591_408 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (591 : Fin 865)
      exact leaf_0_2_591
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (408 : Fin 865)
      exact leaf_0_2_408
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_591_408 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_591_408) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_591_408)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_591_408
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_591_408) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(672,408,79)` of the square `2` of cusp `0`. -/
theorem ch_0_2_672_408 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 2 := by
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
      (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 2 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 2 (slabL 0 (![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_2_672_408 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (-1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (672 : Fin 865)
      exact leaf_0_2_672
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/4) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (408 : Fin 865)
      exact leaf_0_2_408
    · show Work.RTOwed.kleinPt 2 (slabL 0 (slabPt (1/2) (0) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (79 : Fin 865)
      exact leaf_0_2_79
  have hchart := cSimp_eq_chiRep 0 (a := 2) rfl
    ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ] fl_0_2_672_408 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (-1/4) 1, slabPt (1/4) (0) 1, slabPt (1/2) (0) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_2_672_408) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (79 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_2_672_408)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨79⟩ : QbarCW.Cell) fl_0_2_672_408
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨22, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (79 : Fin 865)) fl_0_2_672_408) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(813,200,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_813_200 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_813_200 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (813 : Fin 865)
      exact leaf_0_3_813
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (200 : Fin 865)
      exact leaf_0_3_200
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_813_200 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_813_200) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_813_200)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_813_200
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_200) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(828,200,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_828_200 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_828_200 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (828 : Fin 865)
      exact leaf_0_3_828
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (200 : Fin 865)
      exact leaf_0_3_200
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_828_200 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (1/2) (3/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_828_200) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_828_200)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_828_200
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_200) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(744,264,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_744_264 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_744_264 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (744 : Fin 865)
      exact leaf_0_3_744
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (264 : Fin 865)
      exact leaf_0_3_264
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_744_264 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_744_264) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_744_264)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_744_264
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_264) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(762,264,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_762_264 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_762_264 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (762 : Fin 865)
      exact leaf_0_3_762
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (264 : Fin 865)
      exact leaf_0_3_264
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_762_264 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (1/2) (1/4) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_762_264) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_762_264)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_762_264
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_264) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(762,380,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_762_380 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_762_380 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (762 : Fin 865)
      exact leaf_0_3_762
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (380 : Fin 865)
      exact leaf_0_3_380
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_762_380 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (1/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_762_380) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_762_380)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_762_380
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_762_380) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(828,380,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_828_380 :
    cChain 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_828_380 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (828 : Fin 865)
      exact leaf_0_3_828
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (3/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (380 : Fin 865)
      exact leaf_0_3_380
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_828_380 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (3/4) (3/4) 1, slabPt (3/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_828_380) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_828_380)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_828_380
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_828_380) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(744,384,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_744_384 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_744_384 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (744 : Fin 865)
      exact leaf_0_3_744
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (384 : Fin 865)
      exact leaf_0_3_384
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_744_384 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (1/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_744_384) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_744_384)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_744_384
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_744_384) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

/-- The chart identity of the flag `(813,384,72)` of the square `3` of cusp `0`. -/
theorem ch_0_3_813_384 :
    cChain 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ])
      = singGen (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
          (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
          (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384))) := by
  rw [cChain]
  have hbox : ∀ i : Fin 3,
      slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH ∈ Work.RTOwed.cubeBox 3 := by
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
      (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] 2) + Work.RTOwed.cuspH) j
        < (Work.Cusp.cubeCorner 3 j : ℝ) + 1 := by
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
      Work.RTOwed.kleinPt 3 (slabL 0 (![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] i) + Work.RTOwed.cuspH)
        = QbarPD.posR (Mbar.flagIdx fl_0_3_813_384 i) := by
    intro i
    fin_cases i
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (3/4) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (813 : Fin 865)
      exact leaf_0_3_813
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/4) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (384 : Fin 865)
      exact leaf_0_3_384
    · show Work.RTOwed.kleinPt 3 (slabL 0 (slabPt (1/2) (1/2) 1) + Work.RTOwed.cuspH)
        = QbarPD.posR (72 : Fin 865)
      exact leaf_0_3_72
  have hchart := cSimp_eq_chiRep 0 (a := 3) rfl
    ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ] fl_0_3_813_384 (0 : ZMod 2) 2 (denseSimplex3 2) hbox hfar hpos rfl
  rw [show singGen (cSimp 0 (slabV 0 ![ slabPt (1/4) (3/4) 1, slabPt (1/4) (1/2) 1, slabPt (1/2) (1/2) 1 ]))
      = singGen (⟨fun w => Mbar.chiRep ((0 : ZMod 2), fl_0_3_813_384) w,
          Mbar.continuous_chiRep _⟩) from congrArg singGen hchart]
  congr 1
  apply ContinuousMap.ext
  intro w
  have hmo : Mbar.moCell (0 : ZMod 2) (72 : Fin 865)
      = Mbar.moCid (2 : Fin 5) (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2)) := by
    decide
  have hfr : Work.MbarHomology.flagRel ((0 : ZMod 2), fl_0_3_813_384)
      (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384) := by
    have h := Mbar.flagRel_act_facet (0 : ZMod 2) 2 (⟨72⟩ : QbarCW.Cell) fl_0_3_813_384
      (fun i => by
        fin_cases i
        · exact le_of_lt (show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide))
        · exact le_of_lt (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide)
        · exact le_rfl)
    rw [hmo] at h
    exact h
  have hkey : (Mbar.chi 2 (Mbar.rootSimplex 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384))) w
      = Mbar.chiRep (Mbar.moRootC (Mbar.moCid (2 : Fin 5)
        (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))),
        Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384) w :=
    Psi1.chi_rootSimplex_apply 2 (by norm_num)
      (⟨16, by decide⟩ : Fin (Work.HomologyIso.Gen.mbarDim 2))
      (Mbar.flagAct (Mbar.sigVec (0 : ZMod 2) (72 : Fin 865)) fl_0_3_813_384) w
  rw [hkey]
  exact Mbar.chiRep_eq hfr w

end

end Work.BridgeSquare.SlabBuild
