import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend

/-!
# Kernel: the `dropValue` program and the states it runs through

`dropValue_prog` drops the top value of stack 0 (whatever it is: `Val.int`, `Val.nil`, `Val.cons`)
by scanning its self-delimiting encoding with a *unary* pending-subtree counter kept on stack 1
above a frame marker: `dropValue_tok` = one pending subtree, `dropValue_base` = bottom of our own
counter region.  Starting with one token, `cons` pushes one token, `nil`/`iend` pop one, and the
scan stops the first time no token is left -- which by `HvdH.pendFold_enc` /
`HvdH.pendFold_take_pos` is exactly after the full encoding of the top value.

This file holds the definitions and the elementary list/state facts; the `Eval` reasoning lives in
`Submission/Work/Kernel/dropValue.lean`.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- Base (frame) marker glyph of the counter region on stack 1. -/
def dropValue_base : Glyph := .mk 1

/-- Counter token glyph: one pending subtree. -/
def dropValue_tok : Glyph := .mk 0

/-- The counter region of stack 1: `p` tokens above the base marker, above `w`. -/
def dropValue_stk1 (p : ℕ) (w : List Glyph) : List Glyph :=
  List.replicate p dropValue_tok ++ dropValue_base :: w

theorem dropValue_stk1_zero (w : List Glyph) : dropValue_stk1 0 w = dropValue_base :: w := by
  simp [dropValue_stk1]

theorem dropValue_stk1_succ (p : ℕ) (w : List Glyph) :
    dropValue_stk1 (p + 1) w = dropValue_tok :: dropValue_stk1 p w := by
  simp [dropValue_stk1, List.replicate_succ]

theorem dropValue_stk1_headD (p : ℕ) (w : List Glyph) :
    (dropValue_stk1 p w).headD .eos = if p = 0 then dropValue_base else dropValue_tok := by
  cases p with
  | zero => simp [dropValue_stk1]
  | succ q => simp [dropValue_stk1, List.replicate_succ]

theorem dropValue_stk1_tail (p : ℕ) (w : List Glyph) (hp : 1 ≤ p) :
    (dropValue_stk1 p w).tail = dropValue_stk1 (p - 1) w := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  rw [show q + 1 - 1 = q from rfl, dropValue_stk1_succ, List.tail_cons]

/-- The canonical state of the `dropValue` scan: stack 0 holds `l0`, stack 1 holds the unary
counter region with `p` tokens above the *unchanged* tail of stack 1, register 1 mirrors the top of
stack 1 (so that a `loop` on register 1 runs while a token is on top), register 2 is set to the base
marker and register 3 to the token glyph; all other components are those of `s`. -/
def dropValue_iter (s : State) (l0 : List Glyph) (p : ℕ) : State :=
  ((((s.updStk 0 l0).updStk 1 (dropValue_stk1 p (s.stk 1))).updReg 1
      (if p = 0 then dropValue_base else dropValue_tok)).updReg 2 dropValue_base).updReg 3
    dropValue_tok

@[simp] theorem dropValue_iter_stk0 (s : State) (l0 : List Glyph) (p : ℕ) :
    (dropValue_iter s l0 p).stk 0 = l0 := by
  simp [dropValue_iter]

@[simp] theorem dropValue_iter_stk1 (s : State) (l0 : List Glyph) (p : ℕ) :
    (dropValue_iter s l0 p).stk 1 = dropValue_stk1 p (s.stk 1) := by
  simp [dropValue_iter]

@[simp] theorem dropValue_iter_stk (s : State) (l0 : List Glyph) (p : ℕ) (k : Stk)
    (h0 : k ≠ 0) (h1 : k ≠ 1) : (dropValue_iter s l0 p).stk k = s.stk k := by
  simp [dropValue_iter, h0, h1]

@[simp] theorem dropValue_iter_reg1 (s : State) (l0 : List Glyph) (p : ℕ) :
    (dropValue_iter s l0 p).reg 1 = if p = 0 then dropValue_base else dropValue_tok := by
  simp [dropValue_iter]

@[simp] theorem dropValue_iter_reg2 (s : State) (l0 : List Glyph) (p : ℕ) :
    (dropValue_iter s l0 p).reg 2 = dropValue_base := by
  simp [dropValue_iter]

@[simp] theorem dropValue_iter_reg3 (s : State) (l0 : List Glyph) (p : ℕ) :
    (dropValue_iter s l0 p).reg 3 = dropValue_tok := by
  simp [dropValue_iter]

@[simp] theorem dropValue_iter_reg (s : State) (l0 : List Glyph) (p : ℕ) (r : Reg)
    (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) : (dropValue_iter s l0 p).reg r = s.reg r := by
  simp [dropValue_iter, h1, h2, h3]

/-- Reading the glyph just popped from stack 0: a `cons` opens a new pending subtree (one more
token), `nil`/`iend` close one (one less), everything else leaves the count alone. -/
def dropValue_chain : Cmd :=
  .ite 2 .cons (.seq (.push 1 3) (.push 1 3))
    (.ite 2 .nil .skip (.ite 2 .iend .skip (.push 1 3)))

/-- One iteration of the scan: pop a token, pop a glyph of the value under examination, update the
token count, reset register 2 and refresh the loop test register 1. -/
def dropValue_body : Cmd :=
  .seq (.pop 1 2) (.seq (.pop 0 2) (.seq dropValue_chain (.seq (.set 2 dropValue_base) (.peek 1 1))))

/-- Set up the counter region on stack 1 (base marker, then one token) and registers 1, 2, 3. -/
def dropValue_pre : Cmd :=
  .seq (.set 3 dropValue_base) (.seq (.push 1 3) (.seq (.set 3 dropValue_tok) (.seq (.push 1 3)
    (.seq (.set 2 dropValue_base) (.set 1 dropValue_tok)))))

/-- Drop the top value of stack 0: set up the counter, scan, drop the counter region. -/
def dropValue_prog : Cmd :=
  .seq dropValue_pre (.seq (.loop 1 dropValue_tok dropValue_body) (.pop 1 0))

/-- Component form of `State.tPop` for the stack that is popped. -/
theorem dropValue_tPop_stk (X : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPop X k r).stk j = if j = k then (X.stk j).tail else X.stk j := by
  by_cases h : j = k <;> simp [State.tPop, h]

/-- Component form of `State.tPop` for the stack that is popped (head variant). -/
theorem dropValue_tPop_reg (X : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPop X k r).reg r' = if r' = r then (X.stk k).headD .eos else X.reg r' := by
  by_cases h : r' = r <;> simp [State.tPop, h]

/-- Component form of `State.tPeek`. -/
theorem dropValue_tPeek_stk (X : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPeek X k r).stk j = X.stk j := by
  simp [State.tPeek]

/-- Component form of `State.tPeek` for the register. -/
theorem dropValue_tPeek_reg (X : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPeek X k r).reg r' = if r' = r then (X.stk k).headD .eos else X.reg r' := by
  by_cases h : r' = r <;> simp [State.tPeek, h]

/-- A `dropValue_iter` state with at least one token has `dropValue_tok` in register 1 (so the
`loop` test succeeds). -/
theorem dropValue_iter_reg1_of_pos (s : State) (l0 : List Glyph) (p : ℕ) (hp : 1 ≤ p) :
    (dropValue_iter s l0 p).reg 1 = dropValue_tok := by
  rw [dropValue_iter_reg1, if_neg (by omega : ¬ p = 0)]

/-- A `dropValue_iter` state with no token left has the base marker in register 1 (so the `loop`
test fails). -/
theorem dropValue_iter_reg1_of_zero (s : State) (l0 : List Glyph) :
    (dropValue_iter s l0 0).reg 1 = dropValue_base := by
  rw [dropValue_iter_reg1, if_pos rfl]

/-- Extensionality for `HvdH.State` (the structure has no generated extensionality lemma). -/
theorem dropValue_state_ext {a b : State} (h1 : ∀ r, a.reg r = b.reg r)
    (h2 : ∀ k, a.stk k = b.stk k) : a = b := by
  cases a with
  | mk r k =>
    cases b with
    | mk r' k' =>
      simp only [State.mk.injEq]
      exact ⟨funext h1, funext h2⟩

/-- Component form of `State.tPush` for the stack. -/
theorem dropValue_compPush_stk (X : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPush X k r).stk j = if j = k then X.reg r :: X.stk j else X.stk j := by
  by_cases h : j = k <;> simp [State.tPush, h]

/-- Component form of `State.tPush` for the registers. -/
theorem dropValue_compPush_reg (X : State) (k : Stk) (r : Reg) (r' : Reg) :
    (State.tPush X k r).reg r' = X.reg r' := by
  simp [State.tPush]

/-- Component form of `State.tSet` for the stack. -/
theorem dropValue_compSet_stk (X : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet X r g).stk j = X.stk j := by
  simp [State.tSet]

/-- Component form of `State.tSet` for the registers. -/
theorem dropValue_compSet_reg (X : State) (r : Reg) (g : Glyph) (r' : Reg) :
    (State.tSet X r g).reg r' = if r' = r then g else X.reg r' := by
  by_cases h : r' = r <;> simp [State.tSet, h]

end Work.Kernel
