import Mathlib
import Submission.Work.IntLib.parseEmitDefs
import Submission.Work.IntLib.Raw

/-!
# `Work.IntLib.drainUntilEval`

Raw `Eval` reasoning for `Work.IntLib.drainUntil` (the "move the part of a stack above the frame
marker `T` onto another stack, dropping `T`" word of `Submission/Work/IntLib/parseEmitDefs.lean`).

* `drainTLoop_eval_aux` is the loop lemma: starting with `s.stk k = gs ++ T :: below` and the test
  register on `eos`, `drainTLoop k k' T r` moves `gs` (reversed) onto stack `k'`, discards `T`, and
  leaves `below` on `k`, at cost `≤ 5 * gs.length + 5`;
* `drainUntilEval` prepends the initial `set r eos` (one extra step).
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- Loop lemma for `drainTLoop`: with `eos` in the test register, the loop pops all glyphs of `gs`
(which are all `≠ T`) from stack `k`, pushes them onto `k'` (reversing them), then pops the marker
`T` (discarding it) and stops with `mk 15` in the test register. -/
theorem drainTLoop_eval_aux (main : Cmd) (k k' : Stk) (hkk : k ≠ k') (T : Glyph) (r : Reg)
    (gs below : List Glyph) (s : State) (hne : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) (hreg : s.reg r = Glyph.eos) :
    ∃ s' n, Eval main (drainTLoop k k' T r) s s' n ∧ n ≤ 5 * gs.length + 5 ∧
      s'.stk k = below ∧ s'.stk k' = gs.reverse ++ s.stk k' ∧ s'.reg r = Glyph.mk 15 ∧
      (∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  induction gs generalizing s with
  | nil =>
    have hstk' : s.stk k = T :: below := by simpa using hstk
    let s1 : State := ⟨Function.update s.reg r T, Function.update s.stk k below⟩
    have h1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hstk'
    let s2 : State := ⟨Function.update s1.reg r (Glyph.mk 15), s1.stk⟩
    have h2 : Eval main (.set r (Glyph.mk 15)) s1 s2 1 := Eval.set_eq
    have hr1 : s1.reg r = T := by simp [s1]
    have hite : Eval main
        (.ite r T (.set r (Glyph.mk 15)) (.seq (.push k' r) (.set r Glyph.eos))) s1 s2 2 :=
      Eval.iteT hr1 h2
    have hbody : Eval main (drainTBody k k' T r) s s2 3 := Eval.seq h1 hite
    have hr2 : s2.reg r = Glyph.mk 15 := by simp [s2]
    have hne2 : s2.reg r ≠ Glyph.eos := by rw [hr2]; decide
    have hloop : Eval main (drainTLoop k k' T r) s2 s2 1 := Eval.loopF hne2
    have hres : Eval main (drainTLoop k k' T r) s s2 5 := Eval.loopT hreg hbody hloop
    refine ⟨s2, 5, hres, ?_, ?_, ?_, hr2, ?_⟩
    · simp
    · simp [s2, s1]
    · simp [s2, s1, Ne.symm hkk]
    · intro j hj1 hj2
      simp [s2, s1, hj1]
  | cons g gs ih =>
    have hstk' : s.stk k = g :: (gs ++ T :: below) := by simpa using hstk
    have hgT : g ≠ T := hne g (by simp)
    have hne' : ∀ x ∈ gs, x ≠ T := fun x hx => hne x (by simp [hx])
    let s1 : State := ⟨Function.update s.reg r g, Function.update s.stk k (gs ++ T :: below)⟩
    have h1 : Eval main (.pop k r) s s1 1 := Eval.pop_cons hstk'
    have hr1 : s1.reg r = g := by simp [s1]
    let s2 : State := ⟨s1.reg, Function.update s1.stk k' (g :: s1.stk k')⟩
    have h2 : Eval main (.push k' r) s1 s2 1 := by
      have h := Eval.push_eq (main := main) (k := k') (r := r) (s := s1) (g := g) hr1
      simpa [s2] using h
    let s3 : State := ⟨Function.update s2.reg r Glyph.eos, s2.stk⟩
    have h3 : Eval main (.set r Glyph.eos) s2 s3 1 := Eval.set_eq
    have h23 : Eval main (.seq (.push k' r) (.set r Glyph.eos)) s1 s3 2 := Eval.seq h2 h3
    have hite : Eval main
        (.ite r T (.set r (Glyph.mk 15)) (.seq (.push k' r) (.set r Glyph.eos))) s1 s3 3 :=
      Eval.iteF (by rw [hr1]; exact hgT) h23
    have hbody : Eval main (drainTBody k k' T r) s s3 4 := Eval.seq h1 hite
    have hstk3 : s3.stk k = gs ++ T :: below := by simp [s3, s2, s1, hkk]
    have hreg3 : s3.reg r = Glyph.eos := by simp [s3]
    obtain ⟨s', n', hev', hn', hk3, hk'3, hr3, hoth3⟩ := ih s3 hne' hstk3 hreg3
    have hloop : Eval main (drainTLoop k k' T r) s s' (4 + n' + 1) := Eval.loopT hreg hbody hev'
    have hcost : 4 + n' + 1 ≤ 5 * (g :: gs).length + 5 := by
      simp only [List.length_cons]; omega
    have hk'fin : s'.stk k' = (g :: gs).reverse ++ s.stk k' := by
      rw [hk'3, List.reverse_cons]
      have hs3k' : s3.stk k' = g :: s.stk k' := by simp [s3, s2, s1, Ne.symm hkk]
      rw [hs3k']
      simp [List.append_assoc]
    have hoth : ∀ j : Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j := by
      intro j hj1 hj2
      rw [hoth3 j hj1 hj2]
      simp [s3, s2, s1, hj1, hj2]
    exact ⟨s', 4 + n' + 1, hloop, hcost, hk3, hk'fin, hr3, hoth⟩

theorem drainUntilEval (main : HvdH.Cmd) (k k' : HvdH.Stk) (hkk : k ≠ k') (T : HvdH.Glyph) (r : HvdH.Reg)
    (gs below : List HvdH.Glyph) (s : HvdH.State) (hne : ∀ g ∈ gs, g ≠ T)
    (hstk : s.stk k = gs ++ T :: below) :
    ∃ (s' : HvdH.State) (n : ℕ), n ≤ 5 * gs.length + 6 ∧
      HvdH.Eval main (Work.IntLib.drainUntil k k' T r) s s' n ∧
      s'.stk k = below ∧ s'.stk k' = gs.reverse ++ s.stk k' ∧ s'.reg r = HvdH.Glyph.mk 15 ∧
      (∀ j : HvdH.Stk, j ≠ k → j ≠ k' → s'.stk j = s.stk j) := by
  let sA : State := ⟨Function.update s.reg r Glyph.eos, s.stk⟩
  have hset : Eval main (.set r Glyph.eos) s sA 1 := Eval.set_eq
  have hregA : sA.reg r = Glyph.eos := by simp [sA]
  have hstkA : sA.stk k = gs ++ T :: below := hstk
  obtain ⟨s', n, hev, hn, hk, hk', hr, hoth⟩ :=
    drainTLoop_eval_aux main k k' hkk T r gs below sA hne hstkA hregA
  refine ⟨s', 1 + n, ?_, Eval.seq hset hev, hk, hk', hr, ?_⟩
  · omega
  · intro j hj1 hj2
    exact hoth j hj1 hj2

end Work.IntLib
