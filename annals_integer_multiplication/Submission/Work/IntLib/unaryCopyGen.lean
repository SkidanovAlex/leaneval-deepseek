import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.unaryCopyDefs
import Submission.Work.IntLib.cpDefs
import Submission.Work.IntLib.cpLoopEval
import Submission.Work.IntLib.UR.phase1_eval
import Submission.Work.Layout.Base

/-!
# `unaryCopyGen`: a `main`-independent unary-counter copy

`Work.IntLib.unaryCopyGen` asks for a **single** program `prog` (chosen before `main` is
quantified) that copies the unary counter `Unary m Ca` of stack `a` onto stack `b`
(whose tail is `gEnd :: Cb`), restoring every other stack, in time `≤ K*(m+1)`.

The witness is `cpProg a b c` (already defined in `Submission/Work/IntLib/cpDefs.lean`) with a
scratch stack `c` obtained from `exists_scratch a b`, and `K = 9`.  Its correctness does not
mention `main` at all: every evaluation lemma used (`cpLoopEval`, `UR.phase1_eval`) has `main`
as a mere parameter.  We therefore restate the specification of `cpProg` with `main` bound
*inside* the universal quantifier (`cpProg_spec`), and derive the requested statement from it.

The program is the same gadget as in `unaryCopyV2`:

1. `set rD gEnd ; push c rD` — sentinel at the bottom of the scratch region of `c`;
2. `peek a rD` — prime the loop register with the head of `a`;
3. `cpLoop a b c` — one iteration per token: pop a token from `a`, push it on `c` and on `b`;
4. `peek c rD ; urPhase1Loop c a ; pop c rD` — move the tokens of `c` back onto `a`, then
   drop the sentinel, restoring `c`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-- **Specification of the copy gadget, independent of `main`.**  With `c` a scratch stack
distinct from `a` and `b`, the program `cpProg a b c` copies the unary counter of `a` onto `b`
in time `≤ 9*(m+1)`, restoring `a` and every stack other than `b`. -/
theorem cpProg_spec (a b c : Stk) (hab : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    ∀ (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) (m : ℕ) (Ca Cb : List Glyph),
      X a = Unary m Ca → X b = gEnd :: Cb →
      ∃ (s' : State) (n : ℕ), Ev main (cpProg a b c) ⟨g, X⟩ s' n ∧ n ≤ 9 * (m + 1) ∧
        s'.stk a = Unary m Ca ∧ s'.stk b = Unary m Cb ∧
        (∀ k : Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  intro main g X m Ca Cb hXa hXb
  have hab' : a ≠ b := fun h => hab h.symm
  have hac : a ≠ c := fun h => hca h.symm
  have hbc : b ≠ c := fun h => hcb h.symm
  -- step 0: `set rD gEnd`
  set g₀ : Reg → Glyph := Function.update g UR.rD gEnd with hg₀
  have e0 : Ev main (.set UR.rD gEnd) ⟨g, X⟩ ⟨g₀, X⟩ 1 := by
    rw [hg₀]; exact ev_set' main UR.rD gEnd g X
  have hg₀rD : g₀ UR.rD = gEnd := by
    rw [hg₀]; exact Function.update_self UR.rD gEnd g
  -- step 1: `push c rD`
  set X₁ : Stk → List Glyph := Function.update X c (gEnd :: X c) with hX₁
  have e1 : Ev main (.push c UR.rD) ⟨g₀, X⟩ ⟨g₀, X₁⟩ 1 := by
    have h := ev_push' main c UR.rD g₀ X
    rw [hg₀rD] at h
    rw [hX₁]; exact h
  have hX₁a : X₁ a = Unary m Ca := by
    rw [hX₁, Function.update_of_ne hac (gEnd :: X c) X, hXa]
  have hX₁b : X₁ b = gEnd :: Cb := by
    rw [hX₁, Function.update_of_ne hbc (gEnd :: X c) X, hXb]
  have hX₁c : X₁ c = gEnd :: X c := by rw [hX₁, Function.update_self]
  -- step 2: `peek a rD`
  set g₁ : Reg → Glyph := Function.update g₀ UR.rD ((X₁ a).headD Glyph.eos) with hg₁
  have e2 : Ev main (.peek a UR.rD) ⟨g₀, X₁⟩ ⟨g₁, X₁⟩ 1 := by
    rw [hg₁]; exact ev_peek' main a UR.rD g₀ X₁
  have hg₁rD : g₁ UR.rD = (Unary m Ca).headD Glyph.eos := by
    rw [hg₁, Function.update_self UR.rD ((X₁ a).headD Glyph.eos) g₀, hX₁a]
  -- step 3: `cpLoop a b c`
  obtain ⟨g₂, X₂, n₂, e3, hn₂, hX₂a, hX₂b, hX₂c, hfr₂⟩ :=
    cpLoopEval main a b c hab' hac hbc m Ca (gEnd :: Cb) (gEnd :: X c)
      g₁ X₁ hX₁a hX₁b hX₁c hg₁rD
  have hX₂b' : X₂ b = Unary m Cb := hX₂b
  have hX₂c' : X₂ c = Unary m (X c) := hX₂c
  -- step 4: `peek c rD`
  set g₃ : Reg → Glyph := Function.update g₂ UR.rD ((X₂ c).headD Glyph.eos) with hg₃
  have e4 : Ev main (.peek c UR.rD) ⟨g₂, X₂⟩ ⟨g₃, X₂⟩ 1 := by
    rw [hg₃]; exact ev_peek' main c UR.rD g₂ X₂
  have hg₃rD : g₃ UR.rD = (Unary m (X c)).headD Glyph.eos := by
    rw [hg₃, Function.update_self UR.rD ((X₂ c).headD Glyph.eos) g₂, hX₂c']
  -- step 5: `urPhase1Loop c a`
  obtain ⟨g₄, X₄, n₄, e5, hn₄, hX₄c, hX₄a, hfr₄⟩ :=
    UR.phase1_eval main c a hca m 0 (X c) Ca g₃ X₂ hX₂c' hX₂a hg₃rD
  have hX₄a' : X₄ a = Unary m Ca := by rw [hX₄a, Nat.zero_add]
  -- step 6: `pop c rD`
  set X₅ : Stk → List Glyph := Function.update X₄ c (X₄ c).tail with hX₅
  set g₅ : Reg → Glyph := Function.update g₄ UR.rD ((X₄ c).headD Glyph.eos) with hg₅
  have e6 : Ev main (.pop c UR.rD) ⟨g₄, X₄⟩ ⟨g₅, X₅⟩ 1 := by
    rw [hg₅, hX₅]; exact ev_pop' main c UR.rD g₄ X₄
  have hX₄c' : X₄ c = gEnd :: X c := by rw [hX₄c, Unary_zero]
  have hX₅c : X₅ c = X c := by rw [hX₅, Function.update_self, hX₄c', List.tail_cons]
  have eall : Ev main (cpProg a b c) ⟨g, X⟩ ⟨g₅, X₅⟩
      (1 + (1 + (1 + (n₂ + (1 + (n₄ + 1)))))) := by
    rw [cpProg]
    exact Ev.seq e0 (Ev.seq e1 (Ev.seq e2 (Ev.seq e3 (Ev.seq e4 (Ev.seq e5 e6)))))
  refine ⟨⟨g₅, X₅⟩, _, eall, ?_, ?_, ?_, ?_⟩
  · -- cost bound
    have h₂ := hn₂
    have h₄ := hn₄
    omega
  · -- stack a is restored
    change X₅ a = Unary m Ca
    rw [show X₅ a = X₄ a from Function.update_of_ne hac (X₄ c).tail X₄]
    exact hX₄a'
  · -- stack b carries the copy
    change X₅ b = Unary m Cb
    rw [show X₅ b = X₂ b from
      (Function.update_of_ne hbc (X₄ c).tail X₄).trans (hfr₄ b hbc hab)]
    exact hX₂b'
  · -- every other stack is untouched
    intro k hka hkb
    change X₅ k = X k
    by_cases hkc : k = c
    · subst hkc; exact hX₅c
    · rw [show X₅ k = X₄ k from Function.update_of_ne hkc (X₄ c).tail X₄,
        hfr₄ k hkc hka, hfr₂ k hka hkb hkc]
      exact Function.update_of_ne hkc (gEnd :: X c) X

theorem unaryCopyGen (a b : HvdH.Stk) (hab : b ≠ a) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph) (m : ℕ) (Ca Cb : List HvdH.Glyph),
      X a = Work.IntLib.Unary m Ca → X b = Work.IntLib.gEnd :: Cb →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧ n ≤ K * (m + 1) ∧
        s'.stk a = Work.IntLib.Unary m Ca ∧ s'.stk b = Work.IntLib.Unary m Cb ∧
        (∀ k : HvdH.Stk, k ≠ a → k ≠ b → s'.stk k = X k) := by
  obtain ⟨c, hca, hcb, -⟩ := exists_scratch a b
  exact ⟨cpProg a b c, 9, cpProg_spec a b c hab hca hcb⟩

end Work.IntLib
