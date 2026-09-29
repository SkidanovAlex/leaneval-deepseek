import Mathlib
import Submission.Work.IntLib.parseEmitDefs
import Submission.Work.Kernel.Raw

/-!
# `splitGlyphEval`: one dispatch step of the `parse` word

This file proves `Work.IntLib.splitGlyphEval`, the local correctness of `splitCmd r`:
if the register `r` holds a glyph `g`, then running `splitCmd r` (in at most 12 steps) leaves
stack 0 and every stack but 1 and 2 unchanged, and pushes exactly the glyphs `inX g` / `inY g`
on stacks 1 / 2.

The proof is a finite case analysis on `g`; the `Eval` derivations are assembled from the raw
toolkit of `Submission/Work/Kernel/Raw.lean` (`eval_set`, `eval_push`, `eval_seq`, `eval_iteT`,
`eval_iteF`, `eval_skip`).
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Kernel

/-! ## The three result states of the dispatch bodies -/

/-- Result state of the body pushing the `x`-bit `b` on stack 1. -/
def tX (X : State) (b : Bool) : State :=
  (X.updReg 6 (Glyph.bit b)).updStk 1 (Glyph.bit b :: X.stk 1)

/-- Result state of the body pushing the `y`-bit `b` on stack 2. -/
def tY (X : State) (b : Bool) : State :=
  (X.updReg 7 (Glyph.bit b)).updStk 2 (Glyph.bit b :: X.stk 2)

/-- Result state of the body pushing the `x`-bit `b1` on stack 1 and the `y`-bit `b2` on stack 2. -/
def tXY (X : State) (b1 b2 : Bool) : State :=
  (((X.updReg 6 (Glyph.bit b1)).updStk 1 (Glyph.bit b1 :: X.stk 1)).updReg 7
    (Glyph.bit b2)).updStk 2 (Glyph.bit b2 :: X.stk 2)

lemma eval_tX (main : Cmd) (X : State) (b : Bool) :
    Eval main (Cmd.set 6 (Glyph.bit b) ;; Cmd.push 1 6) X (tX X b) 2 := by
  have h := eval_seq (eval_set main 6 (Glyph.bit b) X)
    (eval_push main 1 6 (State.tSet X 6 (Glyph.bit b)))
  simpa [tX, State.tSet, State.tPush] using h

lemma eval_tY (main : Cmd) (X : State) (b : Bool) :
    Eval main (Cmd.set 7 (Glyph.bit b) ;; Cmd.push 2 7) X (tY X b) 2 := by
  have h := eval_seq (eval_set main 7 (Glyph.bit b) X)
    (eval_push main 2 7 (State.tSet X 7 (Glyph.bit b)))
  simpa [tY, State.tSet, State.tPush] using h

lemma eval_tXY (main : Cmd) (X : State) (b1 b2 : Bool) :
    Eval main (Cmd.set 6 (Glyph.bit b1) ;; Cmd.push 1 6 ;; Cmd.set 7 (Glyph.bit b2) ;; Cmd.push 2 7)
      X (tXY X b1 b2) 4 := by
  have e1 := eval_set main 6 (Glyph.bit b1) X
  have e2 := eval_push main 1 6 (State.tSet X 6 (Glyph.bit b1))
  have e3 := eval_set main 7 (Glyph.bit b2) (State.tPush (State.tSet X 6 (Glyph.bit b1)) 1 6)
  have e4 := eval_push main 2 7
    (State.tSet (State.tPush (State.tSet X 6 (Glyph.bit b1)) 1 6) 7 (Glyph.bit b2))
  have h := eval_seq e1 (eval_seq e2 (eval_seq e3 e4))
  simpa [tXY, State.tSet, State.tPush] using h

/-! ## The generic "no branch matches" case -/

/-- If `g` is not an input glyph, `splitCmd r` just runs through all nine tests and does nothing. -/
lemma splitCmd_not_inp (main : Cmd) (r : Reg) (X : State) (g : Glyph) (h : X.reg r = g)
    (hg : ∀ a b : Option Bool, g ≠ Glyph.inp a b) : Eval main (splitCmd r) X X 10 := by
  have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; exact hg _ _
  have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; exact hg _ _
  have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; exact hg _ _
  have h4 : X.reg r ≠ Glyph.inp (some false) (some true) := by rw [h]; exact hg _ _
  have h5 : X.reg r ≠ Glyph.inp (some false) (some false) := by rw [h]; exact hg _ _
  have h6 : X.reg r ≠ Glyph.inp (some false) none := by rw [h]; exact hg _ _
  have h7 : X.reg r ≠ Glyph.inp none (some true) := by rw [h]; exact hg _ _
  have h8 : X.reg r ≠ Glyph.inp none (some false) := by rw [h]; exact hg _ _
  have h9 : X.reg r ≠ Glyph.inp none none := by rw [h]; exact hg _ _
  exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3 (eval_iteF h4 (eval_iteF h5
    (eval_iteF h6 (eval_iteF h7 (eval_iteF h8 (eval_iteF h9 (eval_skip main X)))))))))

/-- The `inX` of a glyph that is not an input glyph is empty. -/
lemma inX_eq_nil_of_not_inp (g : Glyph) (hg : ∀ a b : Option Bool, g ≠ Glyph.inp a b) :
    inX g = [] := by
  cases g <;> first | rfl | (exfalso; exact hg _ _ rfl)

/-- The `inY` of a glyph that is not an input glyph is empty. -/
lemma inY_eq_nil_of_not_inp (g : Glyph) (hg : ∀ a b : Option Bool, g ≠ Glyph.inp a b) :
    inY g = [] := by
  cases g <;> first | rfl | (exfalso; exact hg _ _ rfl)

/-- Helper: all nine ite tests of `splitCmd` fail (`n` of them, `n ≤ 9`), then the `else` is run. -/
lemma splitCmd_none_none (main : Cmd) (r : Reg) (X : State)
    (h : X.reg r = Glyph.inp none none) : Eval main (splitCmd r) X X 10 := by
  have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
  have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
  have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; decide
  have h4 : X.reg r ≠ Glyph.inp (some false) (some true) := by rw [h]; decide
  have h5 : X.reg r ≠ Glyph.inp (some false) (some false) := by rw [h]; decide
  have h6 : X.reg r ≠ Glyph.inp (some false) none := by rw [h]; decide
  have h7 : X.reg r ≠ Glyph.inp none (some true) := by rw [h]; decide
  have h8 : X.reg r ≠ Glyph.inp none (some false) := by rw [h]; decide
  exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3 (eval_iteF h4 (eval_iteF h5
    (eval_iteF h6 (eval_iteF h7 (eval_iteF h8 (eval_iteT h (eval_skip main X)))))))))

theorem splitGlyphEval (main : HvdH.Cmd) (r : HvdH.Reg) (X : HvdH.State) (g : HvdH.Glyph)
    (h : X.reg r = g) :
    ∃ (X' : HvdH.State) (n : ℕ), n ≤ 12 ∧ HvdH.Eval main (Work.IntLib.splitCmd r) X X' n ∧
      X'.stk 0 = X.stk 0 ∧ X'.stk 1 = Work.IntLib.inX g ++ X.stk 1 ∧
      X'.stk 2 = Work.IntLib.inY g ++ X.stk 2 ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ 1 → j ≠ 2 → X'.stk j = X.stk j) := by
  rcases g with _ | ⟨a, b⟩ | bb | _ | _ | _ | _ | _ | i
  · -- `eos`: no branch matches
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `g = Glyph.inp a b`
    rcases a with _ | a
    · -- `a = none`
      rcases b with _ | b
      · -- `(none, none)`
        refine ⟨X, 10, by norm_num, splitCmd_none_none main r X h, rfl, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro j _ _ _; rfl
      · -- `(none, some b)`
        cases b
        · -- `(none, some false)`
          refine ⟨tY X false, 10, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
          · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
            have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
            have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; decide
            have h4 : X.reg r ≠ Glyph.inp (some false) (some true) := by rw [h]; decide
            have h5 : X.reg r ≠ Glyph.inp (some false) (some false) := by rw [h]; decide
            have h6 : X.reg r ≠ Glyph.inp (some false) none := by rw [h]; decide
            have h7 : X.reg r ≠ Glyph.inp none (some true) := by rw [h]; decide
            exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3 (eval_iteF h4 (eval_iteF h5
              (eval_iteF h6 (eval_iteF h7 (eval_iteT h (eval_tY main X false))))))))
          · simp [tY]
          · simp [tY]
          · simp [tY]
          · intro j _ hj1 hj2; simp [tY, hj2]
        · -- `(none, some true)`
          refine ⟨tY X true, 9, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
          · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
            have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
            have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; decide
            have h4 : X.reg r ≠ Glyph.inp (some false) (some true) := by rw [h]; decide
            have h5 : X.reg r ≠ Glyph.inp (some false) (some false) := by rw [h]; decide
            have h6 : X.reg r ≠ Glyph.inp (some false) none := by rw [h]; decide
            exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3 (eval_iteF h4 (eval_iteF h5
              (eval_iteF h6 (eval_iteT h (eval_tY main X true)))))))
          · simp [tY]
          · simp [tY]
          · simp [tY]
          · intro j _ hj1 hj2; simp [tY, hj2]
    · -- `a = some a`
      cases a
      · -- `a = false`
        rcases b with _ | b
        · -- `(some false, none)`
          refine ⟨tX X false, 8, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
          · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
            have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
            have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; decide
            have h4 : X.reg r ≠ Glyph.inp (some false) (some true) := by rw [h]; decide
            have h5 : X.reg r ≠ Glyph.inp (some false) (some false) := by rw [h]; decide
            exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3 (eval_iteF h4 (eval_iteF h5
              (eval_iteT h (eval_tX main X false))))))
          · simp [tX]
          · simp [tX]
          · simp [tX]
          · intro j _ hj1 hj2; simp [tX, hj1]
        · -- `(some false, some b)`
          cases b
          · -- `(some false, some false)`
            refine ⟨tXY X false false, 9, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
            · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
              have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
              have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; decide
              have h4 : X.reg r ≠ Glyph.inp (some false) (some true) := by rw [h]; decide
              exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3 (eval_iteF h4
                (eval_iteT h (eval_tXY main X false false)))))
            · simp [tXY]
            · simp [tXY]
            · simp [tXY]
            · intro j _ hj1 hj2; simp [tXY, hj1, hj2]
          · -- `(some false, some true)`
            refine ⟨tXY X false true, 8, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
            · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
              have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
              have h3 : X.reg r ≠ Glyph.inp (some true) none := by rw [h]; decide
              exact eval_iteF h1 (eval_iteF h2 (eval_iteF h3
                (eval_iteT h (eval_tXY main X false true))))
            · simp [tXY]
            · simp [tXY]
            · simp [tXY]
            · intro j _ hj1 hj2; simp [tXY, hj1, hj2]
      · -- `a = true`
        rcases b with _ | b
        · -- `(some true, none)`
          refine ⟨tX X true, 5, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
          · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
            have h2 : X.reg r ≠ Glyph.inp (some true) (some false) := by rw [h]; decide
            exact eval_iteF h1 (eval_iteF h2 (eval_iteT h (eval_tX main X true)))
          · simp [tX]
          · simp [tX]
          · simp [tX]
          · intro j _ hj1 hj2; simp [tX, hj1]
        · -- `(some true, some b)`
          cases b
          · -- `(some true, some false)`
            refine ⟨tXY X true false, 6, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
            · have h1 : X.reg r ≠ Glyph.inp (some true) (some true) := by rw [h]; decide
              exact eval_iteF h1 (eval_iteT h (eval_tXY main X true false))
            · simp [tXY]
            · simp [tXY]
            · simp [tXY]
            · intro j _ hj1 hj2; simp [tXY, hj1, hj2]
          · -- `(some true, some true)`
            refine ⟨tXY X true true, 5, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
            · exact eval_iteT h (eval_tXY main X true true)
            · simp [tXY]
            · simp [tXY]
            · simp [tXY]
            · intro j _ hj1 hj2; simp [tXY, hj1, hj2]
  · -- `bit bb`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `pos`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `neg`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `iend`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `nil`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `cons`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl
  · -- `mk i`
    refine ⟨X, 10, by norm_num, splitCmd_not_inp main r X _ h (by intro a b hh; cases hh),
      rfl, ?_, ?_, ?_⟩
    · rw [inX_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · rw [inY_eq_nil_of_not_inp _ (by intro a b hh; cases hh)]; simp
    · intro j _ _ _; rfl

end Work.IntLib
