import Mathlib
import Submission.Work.IntLib.chunkProg
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.unaryCopyDefs
import Submission.Work.IntLib.cpDefs
import Submission.Work.IntLib.cpLoopEval
import Submission.Work.IntLib.UR.phase1_eval
import Submission.Work.Layout.Base

/-!
# `unaryCopySC`: copy the unary counter of stack `sCB` onto stack `sCW`

The `chunk` word keeps a unary counter `Unary m Ca` on stack `sCB` (`= 9`) and a working counter
`Unary m Cb` on stack `sCW` (`= 8`); this file provides the gadget that copies the former onto the
latter, in time `9*(m+1)`, restoring every other stack (including the scratch stack `scC = 15`).

The program is `cpProg sCB sCW scC` (defined in `Submission/Work/IntLib/cpDefs.lean`):

1. `set rD gEnd ; push scC rD` — put the sentinel `gEnd` at the bottom of the scratch region of
   `scC`, so that `scC` reads as `Unary 0 (X scC)`;
2. `peek sCB rD` — prime the loop register with the head of the counter on `sCB`;
3. `cpLoop sCB sCW scC` — one iteration per token: pop a token from `sCB`, push it on `scC` **and**
   on `sCW`; afterwards `sCB = Unary 0 Ca`, `sCW = Unary m Cb`, `scC = Unary m (X scC)`;
4. `peek scC rD ; urPhase1Loop scC sCB` — move the `m` tokens of `scC` back onto `sCB`,
   giving `sCB = Unary m Ca` and `scC = Unary 0 (X scC)`;
5. `pop scC rD` — drop the sentinel, restoring `scC` to `X scC`.

The program does not depend on `main`, hence the `∃ prog, ∀ main` shape of the statement.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-- Scratch stack of the `sCB → sCW` copy gadget (`15` is used by no other word of `IntLib`). -/
def scC : Stk := 15

/-- The `sCB → sCW` copy gadget (a plain, `main`-independent program). -/
def scProg : Cmd := cpProg sCB sCW scC

theorem unaryCopySC : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd)
    (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph) (m : ℕ)
    (Ca Cb : List HvdH.Glyph),
    X Work.IntLib.sCB = Work.IntLib.Unary m Ca → X Work.IntLib.sCW = Work.IntLib.gEnd :: Cb →
    ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main prog ⟨g, X⟩ s' n ∧ n ≤ K * (m + 1) ∧
      s'.stk Work.IntLib.sCB = Work.IntLib.Unary m Ca ∧
      s'.stk Work.IntLib.sCW = Work.IntLib.Unary m Cb ∧
      (∀ k : HvdH.Stk, k ≠ Work.IntLib.sCB → k ≠ Work.IntLib.sCW → s'.stk k = X k) := by
  refine ⟨scProg, 9, ?_⟩
  intro main g X m Ca Cb hXa hXb
  -- the stacks are pairwise distinct
  have hab : sCB ≠ sCW := by decide
  have hba : sCW ≠ sCB := by decide
  have hac : sCB ≠ scC := by decide
  have hca : scC ≠ sCB := by decide
  have hbc : sCW ≠ scC := by decide
  have hcb : scC ≠ sCW := by decide
  -- (0) `set rD gEnd`
  set g₀ : Reg → Glyph := Function.update g UR.rD gEnd with hg₀
  have e0 : Ev main (.set UR.rD gEnd) ⟨g, X⟩ ⟨g₀, X⟩ 1 := by
    rw [hg₀]; exact ev_set' main UR.rD gEnd g X
  have hg₀rD : g₀ UR.rD = gEnd := by
    rw [hg₀]; exact Function.update_self UR.rD gEnd g
  -- (1) `push scC rD`: the sentinel at the bottom of the scratch region of `scC`
  set X₁ : Stk → List Glyph := Function.update X scC (gEnd :: X scC) with hX₁
  have e1 : Ev main (.push scC UR.rD) ⟨g₀, X⟩ ⟨g₀, X₁⟩ 1 := by
    have h := ev_push' main scC UR.rD g₀ X
    rw [hg₀rD] at h
    rw [hX₁]
    exact h
  have hX₁a : X₁ sCB = Unary m Ca := by
    rw [hX₁, Function.update_of_ne hac (gEnd :: X scC) X, hXa]
  have hX₁b : X₁ sCW = gEnd :: Cb := by
    rw [hX₁, Function.update_of_ne hbc (gEnd :: X scC) X, hXb]
  have hX₁c : X₁ scC = gEnd :: X scC := by rw [hX₁, Function.update_self]
  -- (2) `peek sCB rD`
  set g₁ : Reg → Glyph := Function.update g₀ UR.rD ((X₁ sCB).headD Glyph.eos) with hg₁
  have e2 : Ev main (.peek sCB UR.rD) ⟨g₀, X₁⟩ ⟨g₁, X₁⟩ 1 := by
    rw [hg₁]; exact ev_peek' main sCB UR.rD g₀ X₁
  have hg₁rD : g₁ UR.rD = (Unary m Ca).headD Glyph.eos := by
    rw [hg₁, Function.update_self UR.rD ((X₁ sCB).headD Glyph.eos) g₀, hX₁a]
  -- (3) `cpLoop sCB sCW scC`: move the counter of `sCB` onto both `sCW` and `scC`
  obtain ⟨g₂, X₂, n₂, e3, hn₂, hX₂a, hX₂b, hX₂c, hfr₂⟩ :=
    cpLoopEval main sCB sCW scC hab hac hbc m Ca (gEnd :: Cb) (gEnd :: X scC)
      g₁ X₁ hX₁a hX₁b hX₁c hg₁rD
  have hX₂b' : X₂ sCW = Unary m Cb := hX₂b
  have hX₂c' : X₂ scC = Unary m (X scC) := hX₂c
  -- (4) `peek scC rD`
  set g₃ : Reg → Glyph := Function.update g₂ UR.rD ((X₂ scC).headD Glyph.eos) with hg₃
  have e4 : Ev main (.peek scC UR.rD) ⟨g₂, X₂⟩ ⟨g₃, X₂⟩ 1 := by
    rw [hg₃]; exact ev_peek' main scC UR.rD g₂ X₂
  have hg₃rD : g₃ UR.rD = (Unary m (X scC)).headD Glyph.eos := by
    rw [hg₃, Function.update_self UR.rD ((X₂ scC).headD Glyph.eos) g₂, hX₂c']
  -- (5) `urPhase1Loop scC sCB`: move the `m` tokens back onto `sCB`
  obtain ⟨g₄, X₄, n₄, e5, hn₄, hX₄c, hX₄a, hfr₄⟩ :=
    UR.phase1_eval main scC sCB hca m 0 (X scC) Ca g₃ X₂ hX₂c' hX₂a hg₃rD
  have hX₄a' : X₄ sCB = Unary m Ca := by rw [hX₄a, Nat.zero_add]
  -- (6) `pop scC rD`: drop the sentinel, restoring `scC`
  set X₅ : Stk → List Glyph := Function.update X₄ scC (X₄ scC).tail with hX₅
  set g₅ : Reg → Glyph := Function.update g₄ UR.rD ((X₄ scC).headD Glyph.eos) with hg₅
  have e6 : Ev main (.pop scC UR.rD) ⟨g₄, X₄⟩ ⟨g₅, X₅⟩ 1 := by
    rw [hg₅, hX₅]; exact ev_pop' main scC UR.rD g₄ X₄
  have hX₄c' : X₄ scC = gEnd :: X scC := by rw [hX₄c, Unary_zero]
  have hX₅c : X₅ scC = X scC := by rw [hX₅, Function.update_self, hX₄c', List.tail_cons]
  -- the six steps compose into the program
  have eall : Ev main scProg ⟨g, X⟩ ⟨g₅, X₅⟩
      (1 + (1 + (1 + (n₂ + (1 + (n₄ + 1)))))) := by
    simp only [scProg]
    rw [cpProg]
    exact Ev.seq e0 (Ev.seq e1 (Ev.seq e2 (Ev.seq e3 (Ev.seq e4 (Ev.seq e5 e6)))))
  refine ⟨⟨g₅, X₅⟩, _, eall, ?_, ?_, ?_, ?_⟩
  · -- cost bound: `3 + (5m+1) + 1 + (4m+2) + 1 ≤ 9*(m+1)`
    omega
  · -- stack `sCB` is restored
    change X₅ sCB = Unary m Ca
    rw [show X₅ sCB = X₄ sCB from Function.update_of_ne hac (X₄ scC).tail X₄]
    exact hX₄a'
  · -- stack `sCW` carries the copy
    change X₅ sCW = Unary m Cb
    rw [show X₅ sCW = X₂ sCW from
      (Function.update_of_ne hbc (X₄ scC).tail X₄).trans (hfr₄ sCW hbc hba)]
    exact hX₂b'
  · -- every other stack is untouched
    intro k hka hkb
    change X₅ k = X k
    by_cases hkc : k = scC
    · subst hkc; exact hX₅c
    · rw [show X₅ k = X₄ k from Function.update_of_ne hkc (X₄ scC).tail X₄,
        hfr₄ k hkc hka, hfr₂ k hka hkb hkc]
      exact Function.update_of_ne hkc (gEnd :: X scC) X

end Work.IntLib
