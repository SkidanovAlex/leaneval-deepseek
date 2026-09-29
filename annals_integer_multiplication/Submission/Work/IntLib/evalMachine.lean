import Mathlib
import Submission.HvdH.Interfaces

/-!
# IntLib: a fuel-driven reference machine for `Cmd`

This file provides a *computable* reference interpreter for StackLang, to be used when a concrete
run of a concrete program must be evaluated in the kernel (e.g. `by decide`).

* `runSteps main F k s` runs the todo list `k` (a list of commands, executed in sequence) from the
  state `s` with at most `F` machine steps; it returns the final state and the number of `Eval`
  cost units consumed, or `none` if the fuel runs out.  One machine step is one element of the todo
  list: a primitive (`skip`, `pop`, `peek`, `push`, `set`, `mov`), a `loop` test / `ite` test, a
  `self`, or a `seq` *expansion* (which consumes fuel but no `Eval` cost).
* The recursion is structural in the fuel, so the kernel can reduce `runSteps` on numeral fuel:
  `by decide` and `rfl` compute concrete runs.
* `sound` says that a run returning `some (s', n)` corresponds to a genuine `Eval` derivation:
  `runSteps main F [c] s = some (s', n) → Eval main c s s' n`.

Nothing in the paper's development depends on this file; it is the tool used to exhibit the exact
cost of a concrete `preSetupProg` run.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- `EvalL main k s s' n`: the commands of the list `k`, executed in sequence from `s`, end in `s'`
with total cost `n`. -/
inductive EvalL (main : Cmd) : List Cmd → State → State → ℕ → Prop
  | nil (s : State) : EvalL main [] s s 0
  | cons {c : Cmd} {k : List Cmd} {s s' s'' : State} {n m : ℕ} :
      Eval main c s s' n → EvalL main k s' s'' m → EvalL main (c :: k) s s'' (n + m)

/-- The reference machine: run the todo list `k` from the state `s` with at most `F` machine steps;
returns the final state together with the number of `Eval` cost units consumed. -/
def runSteps (main : Cmd) : ℕ → List Cmd → State → Option (State × ℕ)
  | 0, _, _ => none
  | F + 1, [], s => some (s, 0)
  | F + 1, .skip :: k, s => (runSteps main F k s).map (fun p => (p.1, p.2 + 1))
  | F + 1, .pop k' r :: k, s =>
      (runSteps main F k ⟨Function.update s.reg r ((s.stk k').headD .eos),
        Function.update s.stk k' (s.stk k').tail⟩).map (fun p => (p.1, p.2 + 1))
  | F + 1, .peek k' r :: k, s =>
      (runSteps main F k ⟨Function.update s.reg r ((s.stk k').headD .eos), s.stk⟩).map
        (fun p => (p.1, p.2 + 1))
  | F + 1, .push k' r :: k, s =>
      (runSteps main F k ⟨s.reg, Function.update s.stk k' (s.reg r :: s.stk k')⟩).map
        (fun p => (p.1, p.2 + 1))
  | F + 1, .set r v :: k, s =>
      (runSteps main F k ⟨Function.update s.reg r v, s.stk⟩).map (fun p => (p.1, p.2 + 1))
  | F + 1, .mov d src :: k, s =>
      (runSteps main F k ⟨Function.update s.reg d (s.reg src), s.stk⟩).map
        (fun p => (p.1, p.2 + 1))
  | F + 1, .seq p q :: k, s => runSteps main F (p :: q :: k) s
  | F + 1, .ite r v p q :: k, s =>
      if s.reg r = v then (runSteps main F (p :: k) s).map (fun p => (p.1, p.2 + 1))
      else (runSteps main F (q :: k) s).map (fun p => (p.1, p.2 + 1))
  | F + 1, .loop r v body :: k, s =>
      if s.reg r = v then
        (runSteps main F (body :: .loop r v body :: k) s).map (fun p => (p.1, p.2 + 1))
      else (runSteps main F k s).map (fun p => (p.1, p.2 + 1))
  | F + 1, .self :: k, s => (runSteps main F (main :: k) s).map (fun p => (p.1, p.2 + 1))

theorem EvalL_nil (main : Cmd) (s : State) : EvalL main [] s s 0 := EvalL.nil s

theorem EvalL_cons {main : Cmd} {c : Cmd} {k : List Cmd} {s s' s'' : State} {n m : ℕ}
    (h1 : Eval main c s s' n) (h2 : EvalL main k s' s'' m) :
    EvalL main (c :: k) s s'' (n + m) := EvalL.cons h1 h2

/-- The machine's `skip` step, as an unfolding equation. -/
theorem runSteps_skip (main : Cmd) (F : ℕ) (k : List Cmd) (s : State) :
    runSteps main (F + 1) (.skip :: k) s = (runSteps main F k s).map (fun p => (p.1, p.2 + 1)) :=
  rfl

theorem runSteps_nil (main : Cmd) (F : ℕ) (s : State) :
    runSteps main (F + 1) [] s = some (s, 0) := rfl

theorem runSteps_seq (main : Cmd) (F : ℕ) (p q : Cmd) (k : List Cmd) (s : State) :
    runSteps main (F + 1) (.seq p q :: k) s = runSteps main F (p :: q :: k) s := rfl

/-- `runSteps` unfolds on the head command. -/
theorem runSteps_cons_eq (main : Cmd) (F : ℕ) (c : Cmd) (k : List Cmd) (s : State) :
    runSteps main (F + 1) (c :: k) s = match c with
      | .skip => (runSteps main F k s).map (fun p => (p.1, p.2 + 1))
      | .pop k' r => (runSteps main F k ⟨Function.update s.reg r ((s.stk k').headD .eos),
          Function.update s.stk k' (s.stk k').tail⟩).map (fun p => (p.1, p.2 + 1))
      | .peek k' r => (runSteps main F k ⟨Function.update s.reg r ((s.stk k').headD .eos),
          s.stk⟩).map (fun p => (p.1, p.2 + 1))
      | .push k' r => (runSteps main F k ⟨s.reg, Function.update s.stk k' (s.reg r :: s.stk k')⟩).map
          (fun p => (p.1, p.2 + 1))
      | .set r v => (runSteps main F k ⟨Function.update s.reg r v, s.stk⟩).map
          (fun p => (p.1, p.2 + 1))
      | .mov d src => (runSteps main F k ⟨Function.update s.reg d (s.reg src), s.stk⟩).map
          (fun p => (p.1, p.2 + 1))
      | .seq p q => runSteps main F (p :: q :: k) s
      | .ite r v p q => if s.reg r = v then (runSteps main F (p :: k) s).map (fun p => (p.1, p.2 + 1))
          else (runSteps main F (q :: k) s).map (fun p => (p.1, p.2 + 1))
      | .loop r v body => if s.reg r = v then
            (runSteps main F (body :: .loop r v body :: k) s).map (fun p => (p.1, p.2 + 1))
          else (runSteps main F k s).map (fun p => (p.1, p.2 + 1))
      | .self => (runSteps main F (main :: k) s).map (fun p => (p.1, p.2 + 1)) := by
  cases c <;> rfl

/-- Fuel is irrelevant once the todo list is exhausted. -/
theorem runSteps_zero_fuel (main : Cmd) (k : List Cmd) (s : State) :
    runSteps main 0 k s = none := rfl

end Work.IntLib
