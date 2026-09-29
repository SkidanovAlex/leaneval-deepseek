import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs

/-!
# `Work.Resample.pbRound`: shared definitions

The round-block lemma `Work.Resample.pbRound` of the `progTensorB` development (paper Theorem 4.1,
the `B̃` half) advances the per-round invariant `Work.Resample.PBInv` by one axis.  This file fixes
the *interface* used by the assembly:

* `RInv` / `RInvG` — a generalized form of `PBInv` in which the data of every non-zero stack is an
  explicit parameter; `PBInv … j` is `RInv` with the concrete data (`PBInv_split`).
* `PBStageCost` / `PBStageCost2` — the cost shapes of the round's preamble (with the array on the
  value stack, resp. already parked on stack `1` while a raw boundary glyph
  `Work.Layout.gMark` lies in the raw part of stack `0`; see
  `Submission/Work/Resample/PB_ROUND_NOTES.md`).
* `PBBracket` — the round budget of the statement of `Work.Resample.pbRound`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Generalized round invariant: the value stack holds `L0`, stack `1` is empty, stacks `2, …, 13`
hold `L2, …, L13` (as lists of values, top first) and every other non-zero stack holds no values. -/
def RInv (L0 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 : List Val) :
    List Val → (Stk → List Val) → Prop :=
  fun vs a => vs = L0 ∧ a 1 = [] ∧ a 2 = L2 ∧ a 3 = L3 ∧ a 4 = L4 ∧ a 5 = L5 ∧ a 6 = L6 ∧
    a 7 = L7 ∧ a 8 = L8 ∧ a 9 = L9 ∧ a 10 = L10 ∧ a 11 = L11 ∧ a 12 = L12 ∧ a 13 = L13 ∧
    (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) →
      a k = [])

/-- Generalized round invariant with an explicit stack-`1` slot (used while the array is parked);
`RInv` is the case `L1 = []`. -/
def RInvG (L1 L0 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 : List Val) :
    List Val → (Stk → List Val) → Prop :=
  fun vs a => vs = L0 ∧ a 1 = L1 ∧ a 2 = L2 ∧ a 3 = L3 ∧ a 4 = L4 ∧ a 5 = L5 ∧ a 6 = L6 ∧
    a 7 = L7 ∧ a 8 = L8 ∧ a 9 = L9 ∧ a 10 = L10 ∧ a 11 = L11 ∧ a 12 = L12 ∧ a 13 = L13 ∧
    (∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) →
      a k = [])

/-- `RInv` is `RInvG` with nothing on the parked stack `1`. -/
theorem RInv_eq_RInvG (L0 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 : List Val) :
    RInv L0 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13
      = RInvG [] L0 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 := rfl

/-- `PBInv` at round `j` is the generalized invariant `RInv` with the concrete data of the round,
together with the five semantic facts about the array, its length, the disc condition and the
marker `M`. -/
theorem PBInv_split (p α : ℕ) (ss ts : List ℕ) (Kb : ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (zs0 : List (ℤ × ℤ)) (M : Val) (rest : List Val) (j : ℕ)
    (vs : List Val) (a : Stk → List Val) :
    PBInv p α ss ts Kb Φ zs0 M rest j vs a ↔
      ((progAxis ss ts Φ j zs0).length = (ss.take j).prod * (ts.drop j).prod ∧
       (∀ z ∈ progAxis ss ts Φ j zs0, inDisc p z) ∧
       PBTab Kb p ts < vsz M ∧ vsz M ≤ PBTab Kb p ts + 3) ∧
      RInv (cvecVal (progAxis ss ts Φ j zs0) :: M :: rest) [intList (ts.drop j)]
        [intList (ss.drop j)] [Val.int α] [Val.int p] [Val.int ((ss.take j).prod)]
        [Val.int ((ts.drop j).prod)] [] [] [] [] [M] [] vs a := by
  unfold PBInv RInv
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
    exact ⟨⟨h2, h3, h4, h5⟩, ⟨h1, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩⟩
  · rintro ⟨⟨h2, h3, h4, h5⟩, ⟨h1, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-- Cost shape of the round's preamble when the array is on the value stack (the classical route,
with the table dropped by `Work.Resample.pbCleanup`). -/
def PBStageCost (Kb p t : ℕ) (arr M : Val) (A s B : ℕ) : ℕ :=
  (vsz arr + 1) + (vsz M + 1) + (HvdH.D + 1) * (p + 2) * (p + 2) + (A.size + 2) * (s.size + 2) +
    (HvdH.D + 1) * (p + 2) * (B.size + 2) * (B.size + 2) + Kb * (t + 1) * (p + 1) ^ Kb

/-- Cost shape of the round's preamble on the route of `PB_ROUND_NOTES.md`: the array is already
parked on stack `1`, the table is built above the raw boundary glyph `Work.Layout.gMark` and the four
arguments of the slice word are pushed on top of the array. -/
def PBStageCost2 (Kb p t : ℕ) (arr : Val) (A s B : ℕ) : ℕ :=
  (vsz arr + 1) + (HvdH.D + 1) * (p + 2) * (p + 2) + (A.size + 2) * (s.size + 2) +
    (HvdH.D + 1) * (p + 2) * (B.size + 2) * (B.size + 2) + Kb * (t + 1) * (p + 1) ^ Kb

/-- The round budget of the statement of `Work.Resample.pbRound` (the factor multiplying `Kc`). -/
def PBBracket (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb
  + ((ss.take j).prod * (ts.drop (j + 1)).prod) *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
       + Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2)
  + ((ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + ss.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ts.getD j 0 + ss.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod * (ts.getD j 0 + ss.getD j 0 + 1)).size + 1)
  + 32 * (ts.prod * (2 * p + 8) + 2)
  + 800 * (HvdH.D * (p + 1))
  + (2 * Work.Resample.PBTab Kb p ts + 5) * (2 * Work.Resample.PBTab Kb p ts + 5)
  + 100

end Work.Resample
