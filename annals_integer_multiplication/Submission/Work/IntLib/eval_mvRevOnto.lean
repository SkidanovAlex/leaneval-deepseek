import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.Raw

/-!
# Reversing a marked stack region onto another stack (`IntLib`)

`mvRevOnto k T k' r` consumes the glyphs of stack `k` lying above the frame marker `T` and pushes
them on top of stack `k'` in reverse order, then drops `T`.  This file proves the raw `Eval`
specification `eval_mvRevOnto`.

The library loop lemma `consume_eval` cannot be used directly here: its handler invariant must be
preserved by an *arbitrary* change of the test register (`hreg`), while the natural invariant for
"pop a glyph, then push it on the other stack" has to record the glyph that sits in the register
between the pop and the push.  We therefore prove the loop specification directly, carrying the
register contents as an ordinary hypothesis of the induction (never inside the invariant).
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- Runs of `consumeLoop k T r (.push k' r)` move the glyphs above the marker `T` of stack `k` onto
stack `k'` in reverse order.  Here `gs` is the part of the region still on `k` and `pre` the part
already moved (so `l = pre ++ gs`), which makes the invariant usable at every intermediate state of
the loop body.  Cost: at most `6 + 5 * gs.length`. -/
theorem consumeLoop_push_rev (main : Cmd) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg)
    (hne : k ≠ k') (bk bk' l : List Glyph) (hT : ∀ g ∈ l, g ≠ T) :
    ∀ (pre gs : List Glyph) (s : State), l = pre ++ gs → s.stk k = gs ++ T :: bk →
      s.stk k' = pre.reverse ++ bk' → s.reg r = Glyph.eos →
      ∃ s' n, Eval main (consumeLoop k T r (.push k' r)) s s' n ∧
        s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧ s'.reg r ≠ Glyph.eos ∧
        n ≤ 6 + 5 * gs.length ∧
        ∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
  intro pre gs
  induction gs generalizing pre with
  | nil =>
    intro s hl hstk hstk' hreg
    have hl' : l = pre := by rw [hl, List.append_nil]
    have hsk : s.stk k = T :: bk := by rw [hstk]; simp
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k bk⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k (T :: s1.stk k)⟩
    let s3 : State := ⟨Function.update s2.reg r (Glyph.mk 0), s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hsk
    have hr1 : s1.reg r = T := by simp [s1]
    have e2 : Eval main (.push k r) s1 s2 1 := by
      have h := Eval.push (main := main) k r s1
      simpa [s2, hr1] using h
    have e3 : Eval main (.set r (Glyph.mk 0)) s2 s3 1 := by
      have h := Eval.set (main := main) r (Glyph.mk 0) s2
      simpa [s3] using h
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (.mk 0)))
        (.seq (.push k' r) (.set r .eos))) s1 s3 3 :=
      Eval.iteT hr1 (Eval.seq e2 e3)
    have hbody : Eval main (consumeStep k T r (.push k' r)) s s3 4 := Eval.seq e1 hite
    have hexit : s3.reg r ≠ Glyph.eos := by simp [s3, s2, s1]
    have hloop : Eval main (consumeLoop k T r (.push k' r)) s3 s3 1 := Eval.loopF hexit
    have hmain : Eval main (consumeLoop k T r (.push k' r)) s s3 6 :=
      Eval.loopT hreg hbody hloop
    refine ⟨s3, 6, hmain, ?_, ?_, hexit, by simp, ?_⟩
    · simp [s3, s2, s1]
    · rw [hl']
      simpa [s3, s2, s1, Function.update_of_ne (Ne.symm hne)] using hstk'
    · intro j hj hj'
      simp [s3, s2, s1, Function.update_of_ne hj]
  | cons g gs' ih =>
    intro s hl hstk hstk' hreg
    have hgT : g ≠ T := hT g (by rw [hl]; simp)
    have hl' : l = (pre ++ [g]) ++ gs' := by rw [hl, List.append_assoc]; simp
    have hstk1 : s.stk k = g :: (gs' ++ T :: bk) := by simpa using hstk
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs' ++ T :: bk)⟩
    let s2 : State := ⟨s1.reg, Function.update s1.stk k' (s1.reg r :: s1.stk k')⟩
    let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
    have e1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hstk1
    have hr1 : s1.reg r = g := by simp [s1]
    have e2 : Eval main (.push k' r) s1 s2 1 := by
      have h := Eval.push (main := main) k' r s1
      simpa [s2] using h
    have e3 : Eval main (.set r Glyph.eos) s2 s3 1 := by
      have h := Eval.set (main := main) r Glyph.eos s2
      simpa [s3] using h
    have hite : Eval main (.ite r T (.seq (.push k r) (.set r (.mk 0)))
        (.seq (.push k' r) (.set r .eos))) s1 s3 3 :=
      Eval.iteF (by rw [hr1]; exact hgT) (Eval.seq e2 e3)
    have hbody : Eval main (consumeStep k T r (.push k' r)) s s3 4 := Eval.seq e1 hite
    have hstk3 : s3.stk k = gs' ++ T :: bk := by
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hne]
      exact Function.update_self k (gs' ++ T :: bk) s.stk
    have hstk3' : s3.stk k' = (pre ++ [g]).reverse ++ bk' := by
      simp only [s3, s2, s1]
      rw [Function.update_self, Function.update_self, Function.update_of_ne (Ne.symm hne),
        hstk']
      simp [List.reverse_append]
    have hreg3 : s3.reg r = Glyph.eos := by simp [s3]
    obtain ⟨s', n', hev', hk', hk'', hreg', hn', hfr'⟩ :=
      ih (pre ++ [g]) s3 hl' hstk3 hstk3' hreg3
    have hmain : Eval main (consumeLoop k T r (.push k' r)) s s' (4 + n' + 1) :=
      Eval.loopT hreg hbody hev'
    refine ⟨s', 4 + n' + 1, hmain, hk', hk'', hreg', ?_, ?_⟩
    · have : (g :: gs').length = gs'.length + 1 := by simp
      omega
    · intro j hj hj'
      rw [hfr' j hj hj']
      simp only [s3, s2, s1]
      rw [Function.update_of_ne hj', Function.update_of_ne hj]

/-- `consume k T r (.push k' r)`: move the region of `k` above the marker `T` onto `k'`, reversed,
leaving `T` on top of `k`; the other stacks are untouched.  Cost `≤ 5 * l.length + 8`. -/
theorem consume_push_rev (main : Cmd) (k : Stk) (T : Glyph) (k' : Stk) (r : Reg)
    (l bk bk' : List Glyph) (hne : k ≠ k') (hT : ∀ g ∈ l, g ≠ T) (s : State)
    (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk') :
    ∃ s' n, Eval main (consume k T r (.push k' r)) s s' n ∧
      n ≤ 5 * l.length + 8 ∧
      s'.stk k = T :: bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      ∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
  have h1 : Eval main (.set r Glyph.eos) s ⟨Function.update s.reg r Glyph.eos, s.stk⟩ 1 :=
    Eval.set_eq
  obtain ⟨s', n', hev', hk1, hk2, hreg', hn', hfr'⟩ :=
    consumeLoop_push_rev main k T k' r hne bk bk' l hT [] l
      ⟨Function.update s.reg r Glyph.eos, s.stk⟩ (by simp) (by simpa using hk)
      (by simp [hk']) (by simp)
  refine ⟨s', 1 + n', Eval.seq h1 hev', by omega, hk1, hk2, hfr'⟩

/-- `mvRevOnto k T k' r`: move the region of stack `k` above its marker `T` onto stack `k'`,
reversed, then drop `T`.  Cost `≤ 6 * (l.length + 1) + 9`. -/
theorem eval_mvRevOnto (main : HvdH.Cmd) (k : HvdH.Stk) (T : HvdH.Glyph) (k' : HvdH.Stk)
    (r : HvdH.Reg) (l bk bk' : List HvdH.Glyph) (s : HvdH.State)
    (hT : ∀ g ∈ l, g ≠ T) (hk : s.stk k = l ++ T :: bk) (hk' : s.stk k' = bk')
    (hne : k ≠ k') :
    ∃ s' n, HvdH.Eval main (Work.IntLib.mvRevOnto k T k' r) s s' n ∧
      n ≤ 6 * (l.length + 1) + 9 ∧
      s'.stk k = bk ∧ s'.stk k' = l.reverse ++ bk' ∧
      ∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
  obtain ⟨s₁, n₁, hev₁, hn₁, hk₁, hk₁', hfr₁⟩ :=
    consume_push_rev main k T k' r l bk bk' hne hT s hk hk'
  refine ⟨⟨Function.update s₁.reg r T, Function.update s₁.stk k bk⟩, n₁ + 1,
    Eval.seq hev₁ (Eval.pop_cons (main := main) hk₁), by omega, ?_, ?_, ?_⟩
  · simp
  · simpa [Function.update_of_ne (Ne.symm hne)] using hk₁'
  · intro j hj hj'
    simpa [Function.update_of_ne hj] using hfr₁ j hj hj'

end Work.IntLib
