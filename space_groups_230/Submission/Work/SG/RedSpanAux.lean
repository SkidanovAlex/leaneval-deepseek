import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# Reduction by an echelon basis: auxiliary vocabulary

This file holds the definitions shared by the proof of `Work.SG.RepCoh_redspan` and the lemmas
delegated for it.

`Data.reduceBl Bl x` performs, for `c = 0, 1, …, Bl.length - 1`, the elimination step
`x ↦ x - ⌊x_c / (row_c)_c⌋ • row_c` (integer division, and `zipWith` truncating to the shorter
list).  Consequently `x - reduceBl Bl x` is a `ℤ`-combination of the rows of `Bl`, with
coefficients the quotients chosen along the way — the content of `RepCoh_redspan`.

Nothing here is `sorry`ed.
-/

namespace Work.SG

namespace RS

open Work.SG.RC (BlR linC vsub BlR_getD)

/-- Row `c` of `Bl`, as a flat vector. -/
def rowc (Bl : List (List ℤ × Data.V3)) (c : ℕ) : List ℤ := (Bl.getD c ([], Data.V3.zero)).1

theorem rowc_eq_BlR (Bl : List (List ℤ × Data.V3)) (c : ℕ) : rowc Bl c = (BlR Bl).getD c [] :=
  (BlR_getD Bl c).symm

/-- The quotient by which row `c` is subtracted in the elimination step applied to `y`. -/
def quot (Bl : List (List ℤ × Data.V3)) (y : List ℤ) (c : ℕ) : ℤ :=
  y.getD c 0 / (rowc Bl c).getD c 1

/-- One elimination step at column `c`: `y ↦ y - ⌊y_c / (row_c)_c⌋ • row_c`. -/
def redS (Bl : List (List ℤ × Data.V3)) (y : List ℤ) (c : ℕ) : List ℤ :=
  List.zipWith (fun a b => a - quot Bl y c * b) y (rowc Bl c)

/-- `n` elimination steps at columns `0, …, n-1` (in that order). -/
def redN (Bl : List (List ℤ × Data.V3)) : ℕ → List ℤ → List ℤ
  | 0, y => y
  | n + 1, y => redS Bl (redN Bl n y) n

/-- The quotients chosen by the first `n` steps of the reduction of `x`. -/
def qsL (Bl : List (List ℤ × Data.V3)) (x : List ℤ) (n : ℕ) : List ℤ :=
  (List.range n).map (fun c => quot Bl (redN Bl c x) c)

/-- Coordinate form of the difference of two flat vectors. -/
theorem vsub_getD {x y : List ℤ} {q : ℕ} (hx : q < x.length) (hy : q < y.length) :
    (vsub x y).getD q 0 = x.getD q 0 - y.getD q 0 := by
  have hz : q < (vsub x y).length := by
    simp only [vsub, List.length_zipWith]; omega
  simp only [vsub] at hz ⊢
  rw [List.getD_eq_getElem _ _ hz, List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy,
    List.getElem_zipWith]

/-- `Data.reduceBl` is the `n`-step reduction `redN` with `n = Bl.length`. -/
theorem range_foldl_eq_redN (Bl : List (List ℤ × Data.V3)) (x : List ℤ) :
    ∀ n, (List.range n).foldl (fun y c => redS Bl y c) x = redN Bl n x
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.foldl_append, range_foldl_eq_redN Bl x n]
      rfl

theorem reduceBl_eq_redN (Bl : List (List ℤ × Data.V3)) (x : List ℤ) :
    Data.reduceBl Bl x = redN Bl Bl.length x := by
  have h : Data.reduceBl Bl x = (List.range Bl.length).foldl (fun y c => redS Bl y c) x := by
    simp only [Data.reduceBl, redS, quot, rowc]
  rw [h, range_foldl_eq_redN]

end RS

end Work.SG
