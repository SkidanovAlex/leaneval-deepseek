import Mathlib
import Submission.Work.Compiler.Defs

namespace Work.Compiler

open HvdH

/-- Every `HvdH.Eval` step increases a single stack's length by at most one. -/
theorem stack_len_le {main c : HvdH.Cmd} {s s' : HvdH.State} {n : ℕ} (h : HvdH.Eval main c s s' n)
    (k : HvdH.Stk) : (s'.stk k).length ≤ (s.stk k).length + n := by
  induction h with
  | skip s => omega
  | pop k0 r s =>
      show (Function.update s.stk k0 (s.stk k0).tail k).length ≤ (s.stk k).length + 1
      rw [Function.update_apply]
      split_ifs with hk
      · subst hk
        simp only [List.length_tail]
        omega
      · omega
  | peek k0 r s =>
      show (s.stk k).length ≤ (s.stk k).length + 1
      omega
  | push k0 r s =>
      show (Function.update s.stk k0 (s.reg r :: s.stk k0) k).length ≤ (s.stk k).length + 1
      rw [Function.update_apply]
      split_ifs with hk
      · subst hk
        simp only [List.length_cons]
        omega
      · omega
  | set r c s =>
      show (s.stk k).length ≤ (s.stk k).length + 1
      omega
  | mov dst src s =>
      show (s.stk k).length ≤ (s.stk k).length + 1
      omega
  | seq h1 h2 ih1 ih2 => omega
  | iteT hr hsub ih => omega
  | iteF hr hsub ih => omega
  | loopF hr => omega
  | loopT hr hbody hloop ihbody ihloop => omega
  | self hsub ih => omega

end Work.Compiler
