import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paProofs1

/-!
# Mirror definitions for the `B̃` half of paper Theorem 4.1 (lead-owned, 2026-09-29)

`progTensorB` is built as a MIRROR of the proved `Ã` half (`paDefs`, `paSetupE`, `paStageE`, `paApplyE`,
`paIter`, `paFinalD`, `paCostD`, `paFinApproxD`, `progTensorA`). The array flows from shape `ts` (input,
`ts.prod` entries) to shape `ss` (output): axis `j` applies the 1-D slice word `q` of `SliceSpecAt`
(length `t_j` ↦ length `s_j`) through `LayoutLib.applyAlong` with arguments
`A = (ss.take j).prod`, `m = t_j`, `n = s_j`, `B = (ts.drop (j+1)).prod`, i.e. the list-level iteration is
`axisIter ts ss Φ` (note the swapped list arguments). Every definition below is the `pa` one with
`ss ↔ ts` swapped in the data flow; size bounds keep `ts.prod` (the larger shape: `sᵢ < tᵢ`), and the
per-axis budget gains the `B`-slice word's extra `Kb (t+1) (p+1)²` term.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The array at axis `j` of the `B̃` pass. -/
def PB2Vec (p : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (j : ℕ) (arr : Val) : Prop :=
  arr = cvecVal (axisIter ts ss Φ j zs0) ∧
  (axisIter ts ss Φ j zs0).length = (ss.take j).prod * (ts.drop j).prod ∧
  (∀ z ∈ axisIter ts ss Φ j zs0, HvdH.inDisc p z) ∧
  vsz arr ≤ ts.prod * (2 * p + 8) + ts.prod + 1

/-- Between-axes invariant: stack 0 holds the array, stack 2 the remaining INPUT dims `ts.drop j`,
stack 3 the remaining OUTPUT dims `ss.drop j`, 4 = α, 5 = p, 6 = the running outer product
`(ss.take j).prod`; every other non-zero stack holds no values. -/
def PB2Inv (p α : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (j : ℕ) (vs rest : List Val) (a : Stk → List Val) : Prop :=
  ∃ arr : Val, PB2Vec p ss ts Φ zs0 j arr ∧ vs = [arr] ∧
    a 1 = [] ∧ a 2 = [intList (ts.drop j)] ∧ a 3 = [intList (ss.drop j)] ∧
    a 4 = [Val.int α] ∧ a 5 = [Val.int p] ∧ a 6 = [Val.int ((ss.take j).prod)] ∧
    (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) → a k = [])

/-- Mid-axis state: the four `applyAlong` arguments, the array, then the table `Pj`. -/
def PB2Mid (Kb : ℕ) (p α : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (j : ℕ) (Pj : List Val)
    (vs rest : List Val) (a : Stk → List Val) : Prop :=
  ∃ arr : Val, PB2Vec p ss ts Φ zs0 j arr ∧
    vs = [Val.int ((ss.take j).prod), Val.int (ts.getD j 0), Val.int (ss.getD j 0),
        Val.int ((ts.drop (j + 1)).prod), arr] ++ Pj ∧
    (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) ∧
    a 1 = [] ∧ a 2 = [intList (ts.drop (j + 1))] ∧ a 3 = [intList (ss.drop (j + 1))] ∧
    a 4 = [Val.int α] ∧ a 5 = [Val.int p] ∧ a 6 = [Val.int ((ss.take j).prod)] ∧
    a 7 = [Val.int (ss.getD j 0)] ∧
    (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6, 7} : Finset ℕ) → a k = [])

/-- Per-axis budget of the `B̃` pass (`PABr` with the swapped products, plus the `B`-word's
`Kb (t+1) (p+1)²` per slice). -/
def PB2Br (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  64 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb)
  + 64 * (((ss.take j).prod * (ts.drop (j + 1)).prod) *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) +
        Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2))
  + 64 * (((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
  + 64 * (isz ((ss.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) + isz ((ts.getD j 0 : ℕ) : ℤ) +
      isz (((ts.drop (j + 1)).prod : ℕ) : ℤ))
  + 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2)
  + 1048576 * ((HvdH.D + 1) * (p + 2))
  + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
  + 1048576 * ((p + 3) * (p + 3))
  + 1000000

/-- Total budget of the `D` axis passes. -/
def PB2IterBrF (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) : ℕ :=
  (∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j) + 1

end Work.Resample
