import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.IntLib.encodeNatBridge

/-!
# `labFold`: shared definitions and elementary facts

`Work.MainP.labFold` asks for a StackLang *fold* combinator: given a word `step` that, from a state
whose value stack is `int l[i] :: int (P i) :: ofList (AC i) :: acc`, produces
`int (P (i+1)) :: ofList (AC (i+1)) :: acc` at cost `Cnt i`, produce a program that walks the
`cons`-chain `intList l` sitting on stack 7 (unaffecting the rest `Y7`), applies `step` once per
element, and leaves `int (P l.length) :: ofList (AC l.length) :: acc` on stack 0.

The program (this is the same shape as `Work.Resample.pbFoldProg`):

* `labBody step` — one round: peek the head glyph of stack 7 into the test register `labR`; at `cons`
  pop it, `Work.Layout.mvVal` the exposed element from stack 7 to the top of stack 0, run `step`,
  and re-arm `labR`; at `nil` pop it and disarm;
* `labLoop step` — the `loop` on `labR`; `labProg step` — re-arm `labR` first.

`labInv` is the loop invariant (after `i` rounds), `labFin` the final state, `labBd` the per-round
cost.  Everything here is `sorry`-free: definitions and re-writings only.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH
open Work.Layout

/-! ## Stacks, registers, program -/

/-- the counter pile holding the `cons`-chain `intList l` while it is folded -/
def labElt : Stk := 7
/-- scratch stack of the `mvVal` move inside the fold loop -/
def labS1 : Stk := 14
/-- second scratch stack of the `mvVal` move inside the fold loop -/
def labS2 : Stk := 15
/-- the loop-test register of the fold loop (`mvVal` uses registers 0–4) -/
def labR : Reg := 9

/-- The element mover of one round: drop the `cons` glyph and move the exposed value from the
counter pile `labElt` to the top of stack 0. -/
def labRd : Cmd := Cmd.seq (Cmd.pop labElt labR) (mvVal labElt 0 labS1 labS2)

/-- One round of the fold loop. -/
def labBody (step : Cmd) : Cmd :=
  seqs [Cmd.peek labElt labR,
        Cmd.ite labR Glyph.cons
          (seqs [Cmd.pop labElt labR, mvVal labElt 0 labS1 labS2, step, Cmd.set labR Glyph.cons])
          (seqs [Cmd.pop labElt labR, Cmd.set labR Glyph.nil])]

/-- The fold loop (its body runs while the head glyph of `labElt` is `cons`). -/
def labLoop (step : Cmd) : Cmd := Cmd.loop labR Glyph.cons (labBody step)

/-- The fold loop with the loop register armed. -/
def labProg (step : Cmd) : Cmd := Cmd.seq (Cmd.set labR Glyph.cons) (labLoop step)

/-! ## The invariant and the per-round cost -/

/-- After `i` rounds: stack 0 holds `int (P i) :: ofList (AC i) :: acc`, stack 7 the remaining
`cons`-chain `intList (l.drop i)` above `Y7`, every other stack is back to `X`, and `labR` is armed. -/
def labInv (l : List ℕ) (P : ℕ → ℕ) (AC : ℕ → List Val) (acc : List Val) (R Y7 : List Glyph)
    (X : Stk → List Glyph) (i : ℕ) (s : State) : Prop :=
  s.stk 0 = (Val.int ((P i : ℕ) : ℤ)).enc ++ (ofList (AC i)).enc ++ encs acc ++ R ∧
  s.stk 7 = (intList (l.drop i)).enc ++ Y7 ∧
  (∀ k : Stk, k ≠ 0 → k ≠ 7 → s.stk k = X k) ∧
  s.reg labR = Glyph.cons

/-- The state when the loop has stopped: stack 7 is exactly `Y7`, stack 0 is the result, and the
loop register has been disarmed (which is what makes the closing test fail). -/
def labFin (l : List ℕ) (P : ℕ → ℕ) (AC : ℕ → List Val) (acc : List Val) (R Y7 : List Glyph)
    (X : Stk → List Glyph) (s : State) : Prop :=
  s.stk 0 = (Val.int ((P l.length : ℕ) : ℤ)).enc ++ (ofList (AC l.length)).enc ++ encs acc ++ R ∧
  s.stk 7 = Y7 ∧
  (∀ k : Stk, k ≠ 0 → k ≠ 7 → s.stk k = X k) ∧
  s.reg labR = Glyph.nil

/-- The cost budget of round `i`. -/
def labBd (l : List ℕ) (Cnt : ℕ → ℕ) (i : ℕ) : ℕ :=
  16 * (vsz (Val.int ((l.getD i 0 : ℕ) : ℤ)) + 1) + Cnt i + 5

/-! ## Elementary facts about the encodings -/

theorem intList_cons (t : ℕ) (l : List ℕ) :
    intList (t :: l) = Val.cons (Val.int (t : ℤ)) (intList l) := rfl

theorem intList_enc_cons (t : ℕ) (l : List ℕ) :
    (intList (t :: l)).enc = Glyph.cons :: (Val.int (t : ℤ)).enc ++ (intList l).enc := rfl

theorem intList_enc_nil : (intList ([] : List ℕ)).enc = [Glyph.nil] := rfl

/-- The `cons`-chain re-reads one step: the head element is exposed above the tail. -/
theorem intList_drop_cons {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    (intList (l.drop i)).enc =
      Glyph.cons :: (Val.int ((l.getD i 0 : ℕ) : ℤ)).enc ++ (intList (l.drop (i + 1))).enc := by
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]
  exact intList_enc_cons _ _

/-- The whole chain has been consumed: only the closing `nil` is left. -/
theorem intList_enc_drop_length (l : List ℕ) :
    (intList (l.drop l.length)).enc = [Glyph.nil] := by
  rw [List.drop_length]
  exact intList_enc_nil

/-- Size of an integer value of a natural: `size + 2`. -/
theorem vsz_val_int_natCast (m : ℕ) : vsz (Val.int ((m : ℕ) : ℤ)) = m.size + 2 := by
  rw [vsz, Work.IntLib.vsz_int, Work.IntLib.isz_eq, Int.natAbs_natCast]

end Work.MainP
