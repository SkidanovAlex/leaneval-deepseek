import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Compiler.Defs
import Submission.Work.Compiler.Steps
import Submission.Work.Compiler.CodeAt
import Submission.Work.Compiler.Sim
import Submission.Work.Compiler.SimSteps
import Submission.Work.Compiler.Sim2
import Submission.Work.Compiler.stack_len_le
import Submission.Work.Compiler.runs_prologue
import Submission.Work.Compiler.runs_epilogue
import Submission.Work.Compiler.codeAt_of_drop
import Submission.Work.Compiler.initList_toTM2
import Submission.Work.Compiler.haltList_toTM2
import Submission.Work.Compiler.TMBridge

/-! Guidance from the project lead (the requester):

AREA OWNER: Compiler. You prove `HvdH.CompilerThm` (Submission/HvdH/Interfaces.lean, lead-owned, do not edit).

The proof is assembled from
* `Defs.lean`      : flat instructions, `compile`, the machine `mach`, the `FinTM2` bundle `toTM2`;
* `Steps.lean`     : one-machine-step computation lemmas for each instruction;
* `CodeAt.lean`    : the position predicate for compiled blocks (plus `codeAt_of_drop`);
* `Sim.lean`, `SimSteps.lean`, `Sim2.lean` : the simulation theorem `simulate`;
* `runs_prologue` / `runs_epilogue` : the word input/output stages;
* `stack_len_le`, `initList_toTM2`, `haltList_toTM2` : the glue and the time bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Compiler

open HvdH Turing StateTransition

/-- The compiled program of `P`, with the trailing `ret`. -/
abbrev prog (P : Cmd) : List Instr := progCode P

theorem code_drop_prog (P : Cmd) : (prog P).drop 0 = compile P 0 ++ [Instr.ret] := rfl

theorem codeAt_prog (P : Cmd) : CodeAt (prog P) 0 P :=
  codeAt_of_drop (rest := [Instr.ret]) (code_drop_prog P)

theorem code_ret_prog (P : Cmd) : (prog P)[clen P]? = some Instr.ret := by
  have h : (prog P)[(compile P 0).length]? = some Instr.ret := by
    rw [prog, progCode, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  rwa [compile_length] at h

/-- StackLang programs compile to Mathlib `FinTM2` machines with linear time overhead. -/
theorem compilerThm : HvdH.CompilerThm := by
  intro α ea f P cost hP
  refine ⟨{ tm := tmP (prog P), inputAlphabet := Equiv.refl InSym,
            outputAlphabet := Equiv.refl Bool, time := fun n => 16 * (cost n + n + 1),
            outputsFun := ?_ }, 16, ?_⟩
  · intro a
    classical
    have hgoal : Nonempty (EvalsToInTime (TM2.step (mach (prog P)))
        (initList (tmP (prog P)) (List.map (Equiv.refl InSym).invFun (ea a)))
        (some (haltList (tmP (prog P)) (List.map (Equiv.refl Bool).invFun (id (f a)))))
        (16 * (cost (ea a).length + (ea a).length + 1))) := by
      rw [show id (f a) = f a from rfl]
      rw [show (Equiv.refl Bool).invFun = id from rfl, list_map_id]
      rw [show (Equiv.refl InSym).invFun = id from rfl, list_map_id]
      obtain ⟨s', n₀, hev, hn₀, hstk⟩ := hP a
      have hout : (f a).length ≤ n₀ := by
        have h1 := stack_len_le hev (1 : Stk)
        rw [hstk (1 : Stk)] at h1
        simp only [HvdH.initState] at h1
        simp at h1
        omega
      have hpro : EvalsToInTime (TM2.step (mach (prog P)))
          (initList (tmP (prog P)) (ea a))
          (some ⟨some (lab (prog P) 0), initMS (prog P),
            toStk (prog P) (initState (ea a)) [] [] []⟩)
          (2 * (ea a).length + 2) := by
        rw [initList_tmP (prog P) (ea a)]
        exact Classical.choice (runs_prologue (prog P) (ea a))
      obtain ⟨σ', hreg', hsim'⟩ := simulate (prog P) P (codeAt_prog P) (code_ret_prog P) hev
        0 (Nat.zero_le _) (codeAt_le (prog P) P 0 (codeAt_prog P)) (codeAt_prog P)
        (initMS (prog P)) [] [] [] rfl
      obtain ⟨hsim⟩ := hsim'
      have hPle : clen P ≤ (prog P).length :=
        le_of_lt (List.getElem?_eq_some_iff.mp (code_ret_prog P)).choose
      rw [show labOf (prog P) (0 + clen P) (codeAt_le (prog P) P 0 (codeAt_prog P))
            = labOf (prog P) (clen P) hPle from labOf_congr (prog P) _ hPle (by omega)] at hsim
      have hretstep := eit_ret_none (prog P) (clen P) hPle (code_ret_prog P) σ' s' [] []
      have hstk_eq : s'.stk = (⟨fun _ => Glyph.eos,
          (fun k : Fin 16 => if k = 1 then (f a).map Glyph.bit else [])⟩ : State).stk := by
        funext k
        rw [hstk k]
      have hstack : toStk (prog P) s' [] [] [] =
          toStk (prog P) ⟨fun _ => Glyph.eos,
            (fun k : Fin 16 => if k = 1 then (f a).map Glyph.bit else [])⟩ [] [] [] :=
        toStk_of_stk_eq hstk_eq [] [] []
      have hepi := Classical.choice (runs_epilogue (prog P) (f a)
        ⟨σ'.reg, σ'.dat, σ'.sym, none⟩)
      rw [← hstack] at hepi
      have h1 := eit_trans hpro hsim
      have h2 := eit_trans h1 hretstep
      have h3 := eit_trans h2 hepi
      rw [haltList_tmP (prog P) (f a)]
      exact ⟨EvalsToInTime.mono' h3 (by omega)⟩
    exact Classical.choice hgoal
  · intro n
    exact le_refl _

end Work.Compiler
