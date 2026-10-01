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
      (fun _ => show (⟨843⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨843⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨843⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide +kernel) (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(855 < 196 < 58)` of `Q̄`. -/
def fl_0_0_855_196 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨855⟩ : QbarCell)) (⟨196⟩ : QbarCell)
      (fun _ => show (⟨855⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨855⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨855⟩ : QbarCell) < (⟨196⟩ : QbarCell) from by decide +kernel) (show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨196⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(780 < 260 < 58)` of `Q̄`. -/
def fl_0_0_780_260 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨780⟩ : QbarCell)) (⟨260⟩ : QbarCell)
      (fun _ => show (⟨780⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨780⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨780⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide +kernel) (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(795 < 260 < 58)` of `Q̄`. -/
def fl_0_0_795_260 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨795⟩ : QbarCell)) (⟨260⟩ : QbarCell)
      (fun _ => show (⟨795⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨795⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨795⟩ : QbarCell) < (⟨260⟩ : QbarCell) from by decide +kernel) (show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨260⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(795 < 332 < 58)` of `Q̄`. -/
def fl_0_0_795_332 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨795⟩ : QbarCell)) (⟨332⟩ : QbarCell)
      (fun _ => show (⟨795⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨795⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨795⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide +kernel) (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(855 < 332 < 58)` of `Q̄`. -/
def fl_0_0_855_332 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨855⟩ : QbarCell)) (⟨332⟩ : QbarCell)
      (fun _ => show (⟨855⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨855⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨855⟩ : QbarCell) < (⟨332⟩ : QbarCell) from by decide +kernel) (show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨332⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(780 < 336 < 58)` of `Q̄`. -/
def fl_0_0_780_336 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨780⟩ : QbarCell)) (⟨336⟩ : QbarCell)
      (fun _ => show (⟨780⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨780⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨780⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide +kernel) (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(843 < 336 < 58)` of `Q̄`. -/
def fl_0_0_843_336 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨843⟩ : QbarCell)) (⟨336⟩ : QbarCell)
      (fun _ => show (⟨843⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide +kernel))
    (⟨58⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨843⟩ : QbarCell) < (⟨58⟩ : QbarCell) from lt_trans (show (⟨843⟩ : QbarCell) < (⟨336⟩ : QbarCell) from by decide +kernel) (show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨336⟩ : QbarCell) < (⟨58⟩ : QbarCell) from by decide +kernel)

/-- The flag `(708 < 228 < 65)` of `Q̄`. -/
def fl_0_1_708_228 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨708⟩ : QbarCell)) (⟨228⟩ : QbarCell)
      (fun _ => show (⟨708⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide +kernel) (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(723 < 228 < 65)` of `Q̄`. -/
def fl_0_1_723_228 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨723⟩ : QbarCell)) (⟨228⟩ : QbarCell)
      (fun _ => show (⟨723⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨228⟩ : QbarCell) from by decide +kernel) (show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨228⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(633 < 292 < 65)` of `Q̄`. -/
def fl_0_1_633_292 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨633⟩ : QbarCell)) (⟨292⟩ : QbarCell)
      (fun _ => show (⟨633⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide +kernel) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(651 < 292 < 65)` of `Q̄`. -/
def fl_0_1_651_292 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨651⟩ : QbarCell)) (⟨292⟩ : QbarCell)
      (fun _ => show (⟨651⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨292⟩ : QbarCell) from by decide +kernel) (show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨292⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(651 < 356 < 65)` of `Q̄`. -/
def fl_0_1_651_356 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨651⟩ : QbarCell)) (⟨356⟩ : QbarCell)
      (fun _ => show (⟨651⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨651⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨651⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide +kernel) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(723 < 356 < 65)` of `Q̄`. -/
def fl_0_1_723_356 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨723⟩ : QbarCell)) (⟨356⟩ : QbarCell)
      (fun _ => show (⟨723⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨723⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨723⟩ : QbarCell) < (⟨356⟩ : QbarCell) from by decide +kernel) (show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨356⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(633 < 360 < 65)` of `Q̄`. -/
def fl_0_1_633_360 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨633⟩ : QbarCell)) (⟨360⟩ : QbarCell)
      (fun _ => show (⟨633⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨633⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨633⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide +kernel) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(708 < 360 < 65)` of `Q̄`. -/
def fl_0_1_708_360 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨708⟩ : QbarCell)) (⟨360⟩ : QbarCell)
      (fun _ => show (⟨708⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide +kernel))
    (⟨65⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨708⟩ : QbarCell) < (⟨65⟩ : QbarCell) from lt_trans (show (⟨708⟩ : QbarCell) < (⟨360⟩ : QbarCell) from by decide +kernel) (show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨360⟩ : QbarCell) < (⟨65⟩ : QbarCell) from by decide +kernel)

/-- The flag `(672 < 232 < 79)` of `Q̄`. -/
def fl_0_2_672_232 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨672⟩ : QbarCell)) (⟨232⟩ : QbarCell)
      (fun _ => show (⟨672⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide +kernel) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(690 < 232 < 79)` of `Q̄`. -/
def fl_0_2_690_232 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨690⟩ : QbarCell)) (⟨232⟩ : QbarCell)
      (fun _ => show (⟨690⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨232⟩ : QbarCell) from by decide +kernel) (show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨232⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(591 < 296 < 79)` of `Q̄`. -/
def fl_0_2_591_296 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨591⟩ : QbarCell)) (⟨296⟩ : QbarCell)
      (fun _ => show (⟨591⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide +kernel) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(612 < 296 < 79)` of `Q̄`. -/
def fl_0_2_612_296 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨612⟩ : QbarCell)) (⟨296⟩ : QbarCell)
      (fun _ => show (⟨612⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨296⟩ : QbarCell) from by decide +kernel) (show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨296⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(612 < 404 < 79)` of `Q̄`. -/
def fl_0_2_612_404 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨612⟩ : QbarCell)) (⟨404⟩ : QbarCell)
      (fun _ => show (⟨612⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨612⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨612⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide +kernel) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(690 < 404 < 79)` of `Q̄`. -/
def fl_0_2_690_404 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨690⟩ : QbarCell)) (⟨404⟩ : QbarCell)
      (fun _ => show (⟨690⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨690⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨690⟩ : QbarCell) < (⟨404⟩ : QbarCell) from by decide +kernel) (show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨404⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(591 < 408 < 79)` of `Q̄`. -/
def fl_0_2_591_408 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨591⟩ : QbarCell)) (⟨408⟩ : QbarCell)
      (fun _ => show (⟨591⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨591⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨591⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide +kernel) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(672 < 408 < 79)` of `Q̄`. -/
def fl_0_2_672_408 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨672⟩ : QbarCell)) (⟨408⟩ : QbarCell)
      (fun _ => show (⟨672⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide +kernel))
    (⟨79⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨672⟩ : QbarCell) < (⟨79⟩ : QbarCell) from lt_trans (show (⟨672⟩ : QbarCell) < (⟨408⟩ : QbarCell) from by decide +kernel) (show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨408⟩ : QbarCell) < (⟨79⟩ : QbarCell) from by decide +kernel)

/-- The flag `(813 < 200 < 72)` of `Q̄`. -/
def fl_0_3_813_200 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨813⟩ : QbarCell)) (⟨200⟩ : QbarCell)
      (fun _ => show (⟨813⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide +kernel) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(828 < 200 < 72)` of `Q̄`. -/
def fl_0_3_828_200 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨828⟩ : QbarCell)) (⟨200⟩ : QbarCell)
      (fun _ => show (⟨828⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨200⟩ : QbarCell) from by decide +kernel) (show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨200⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(744 < 264 < 72)` of `Q̄`. -/
def fl_0_3_744_264 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨744⟩ : QbarCell)) (⟨264⟩ : QbarCell)
      (fun _ => show (⟨744⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide +kernel) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(762 < 264 < 72)` of `Q̄`. -/
def fl_0_3_762_264 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨762⟩ : QbarCell)) (⟨264⟩ : QbarCell)
      (fun _ => show (⟨762⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨264⟩ : QbarCell) from by decide +kernel) (show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨264⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(762 < 380 < 72)` of `Q̄`. -/
def fl_0_3_762_380 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨762⟩ : QbarCell)) (⟨380⟩ : QbarCell)
      (fun _ => show (⟨762⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨762⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨762⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide +kernel) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(828 < 380 < 72)` of `Q̄`. -/
def fl_0_3_828_380 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨828⟩ : QbarCell)) (⟨380⟩ : QbarCell)
      (fun _ => show (⟨828⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨828⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨828⟩ : QbarCell) < (⟨380⟩ : QbarCell) from by decide +kernel) (show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨380⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(744 < 384 < 72)` of `Q̄`. -/
def fl_0_3_744_384 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨744⟩ : QbarCell)) (⟨384⟩ : QbarCell)
      (fun _ => show (⟨744⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨744⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨744⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide +kernel) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

/-- The flag `(813 < 384 < 72)` of `Q̄`. -/
def fl_0_3_813_384 : Simplex QbarCW.Cell 2 :=
  Simplex.snoc (Simplex.snoc (Simplex.vertex (⟨813⟩ : QbarCell)) (⟨384⟩ : QbarCell)
      (fun _ => show (⟨813⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide +kernel))
    (⟨72⟩ : QbarCell)
    (fun i => by
      fin_cases i
      · exact show (⟨813⟩ : QbarCell) < (⟨72⟩ : QbarCell) from lt_trans (show (⟨813⟩ : QbarCell) < (⟨384⟩ : QbarCell) from by decide +kernel) (show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)
      · exact show (⟨384⟩ : QbarCell) < (⟨72⟩ : QbarCell) from by decide +kernel)

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



end

end Work.BridgeSquare.SlabBuild
