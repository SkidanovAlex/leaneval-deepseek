import Mathlib
import Submission.Work.Kernel.dropValueDefs

/-!
# `dropValue_chain` runs in at most four steps

`dropValue_chain` is the glyph-dispatch of the `dropValue` scan (see
`Submission/Work/Kernel/dropValueDefs.lean`): it reads register 2 -- which holds the glyph just
popped from the value under examination -- and pushes `pendStep g 1` copies of the counter token
`dropValue_tok` (from register 3) onto stack 1:

* `cons` opens a new pending subtree, so two tokens are pushed (the test `ite` and the two `push`es:
  cost 3);
* `nil` and `iend` close one, so nothing is pushed (cost 3 resp. 4);
* every other glyph leaves the count alone, so exactly one token is pushed (cost 4).

This file proves that `Eval` follows this description from an *arbitrary* state, which is the form
in which the scan's one-step lemma (`dropValue_body`) consumes it.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- `dropValue_chain` is (definitionally) the nested dispatch on register 2. -/
theorem dropValueChain_unfold :
    dropValue_chain = (.ite 2 Glyph.cons (.seq (.push 1 3) (.push 1 3))
      (.ite 2 Glyph.nil Cmd.skip (.ite 2 Glyph.iend Cmd.skip (.push 1 3)))) := rfl

/-- One `push` of the counter token from register 3, at constant cost 1. -/
theorem dropValueChain_push1 (main : Cmd) (X : State) (h3 : X.reg 3 = dropValue_tok) :
    Eval main (.push 1 3) X (X.updStk 1 (dropValue_tok :: X.stk 1)) 1 := by
  simpa [h3, State.updStk] using Eval.push 1 3 X

/-- The `cons` branch of `dropValue_chain`: two pushes of the counter token, cost 2. -/
theorem dropValueChain_push2 (main : Cmd) (X : State) (h3 : X.reg 3 = dropValue_tok) :
    Eval main (.seq (.push 1 3) (.push 1 3)) X
      (X.updStk 1 (dropValue_tok :: dropValue_tok :: X.stk 1)) 2 := by
  have h1 := dropValueChain_push1 main X h3
  have h2 : Eval main (.push 1 3) (X.updStk 1 (dropValue_tok :: X.stk 1))
      (X.updStk 1 (dropValue_tok :: dropValue_tok :: X.stk 1)) 1 := by
    simpa [h3, State.updStk] using Eval.push 1 3 (X.updStk 1 (dropValue_tok :: X.stk 1))
  exact Eval.seq h1 h2

theorem dropValueChainEval (main : HvdH.Cmd) (X : HvdH.State) (g : HvdH.Glyph)
    (h2 : X.reg 2 = g) (h3 : X.reg 3 = Work.Kernel.dropValue_tok) :
    ∃ c ≤ 4, HvdH.Eval main Work.Kernel.dropValue_chain X
      (X.updStk 1 (List.replicate (HvdH.pendStep g 1) Work.Kernel.dropValue_tok ++ X.stk 1)) c := by
  rcases eq_or_ne g .cons with hg | hg
  · -- `cons`: the test succeeds and both pushes run (cost 1 + 2 = 3)
    subst hg
    refine ⟨3, by norm_num, ?_⟩
    rw [dropValueChain_unfold]
    have hst : List.replicate (HvdH.pendStep HvdH.Glyph.cons 1) Work.Kernel.dropValue_tok ++ X.stk 1
        = Work.Kernel.dropValue_tok :: Work.Kernel.dropValue_tok :: X.stk 1 := rfl
    rw [hst]
    exact Eval.iteT h2 (dropValueChain_push2 main X h3)
  · rcases eq_or_ne g .nil with hg' | hg'
    · -- `nil`: nothing is pushed, but the test still costs a step (cost 1 + 2 = 3)
      subst hg'
      refine ⟨3, by norm_num, ?_⟩
      rw [dropValueChain_unfold]
      have hst : List.replicate (HvdH.pendStep HvdH.Glyph.nil 1) Work.Kernel.dropValue_tok ++ X.stk 1
          = X.stk 1 := by simp
      rw [hst, State.updStk_self]
      exact Eval.iteF (by rw [h2]; decide) (Eval.iteT h2 (Eval.skip X))
    · rcases eq_or_ne g .iend with hg'' | hg''
      · -- `iend`: like `nil`, but two failing tests precede it (cost 1 + 1 + 2 = 4)
        subst hg''
        refine ⟨4, by norm_num, ?_⟩
        rw [dropValueChain_unfold]
        have hst : List.replicate (HvdH.pendStep HvdH.Glyph.iend 1) Work.Kernel.dropValue_tok ++ X.stk 1
            = X.stk 1 := by simp
        rw [hst, State.updStk_self]
        exact Eval.iteF (by rw [h2]; decide)
          (Eval.iteF (by rw [h2]; decide) (Eval.iteT h2 (Eval.skip X)))
      · -- any other glyph: `pendStep g 1 = 1`, one token is pushed (cost 1 + 1 + 1 + 1 = 4)
        refine ⟨4, by norm_num, ?_⟩
        rw [dropValueChain_unfold]
        have hstep : HvdH.pendStep g 1 = 1 := by cases g <;> simp_all [HvdH.pendStep]
        have hst : List.replicate (HvdH.pendStep g 1) Work.Kernel.dropValue_tok ++ X.stk 1
            = Work.Kernel.dropValue_tok :: X.stk 1 := by rw [hstep]; rfl
        rw [hst]
        exact Eval.iteF (by rw [h2]; exact hg) (Eval.iteF (by rw [h2]; exact hg')
          (Eval.iteF (by rw [h2]; exact hg'') (dropValueChain_push1 main X h3)))

end Work.Kernel
