import Mathlib
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.copyIntTo_ev

/-!
# `copyIntB2`: the second loop of `copyIntTo`

`Work.Layout.copyIntB2 t a b rr rf` is the body of the second loop of `copyIntTo`: it peeks the
glyph on top of the scratch stack `t`, stops (setting `rf` to `Glyph.eos`) when it sees the
boundary marker `gMark = Glyph.mk 7`, and otherwise pops the glyph and pushes it onto both stack
`a` and stack `b`, continuing (`rf = Glyph.cons`).

Starting from `X t = D ++ Glyph.mk 7 :: DB` with `Glyph.mk 7 ∉ D`, the loop therefore performs
exactly `D.length + 1` iterations: it restores `D` (in reverse, since `D` was itself obtained by
popping during the first phase) onto *both* `a` and `b`, leaves the marker `Glyph.mk 7` (followed
by `DB`) back on top of `t`, and touches no other stack.  Cost: `6` steps per iteration plus `1`
for the loop test, i.e. `7 * (D.length + 1)`.

This is the public statement of the loop; the same proof is carried out inline (as a private
lemma) in `Submission.Work.Layout.AA.copyIntTo_ev`, which cannot be imported across modules.

* `copyIntB2_step_hit`: an iteration that meets the boundary marker;
* `copyIntB2_step_miss`: an iteration that pops a non-marker glyph;
* `copyIntB2_loop`: the whole loop (the statement of the task).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

private theorem copyIntB2_step_hit (main : Cmd) {t a b : Stk} (rr rf : Reg)
    (g : Reg → Glyph) (X : Stk → List Glyph) {DB : List Glyph}
    (ht : X t = Glyph.mk 7 :: DB) :
    ∃ s' n, Ev main (copyIntB2 t a b rr rf) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk t = Glyph.mk 7 :: DB ∧ s'.stk a = X a ∧ s'.stk b = X b ∧
      (∀ j, s'.stk j = X j) ∧ s'.reg rf = Glyph.eos := by
  have h1 : Ev main (.peek t rr) ⟨g, X⟩ ⟨Function.update g rr (Glyph.mk 7), X⟩ 1 := by
    have h := ev_peek' main t rr g X
    rw [ht, List.headD_cons] at h
    exact h
  have h2 : Ev main (.set rf Glyph.eos) ⟨Function.update g rr (Glyph.mk 7), X⟩
      ⟨Function.update (Function.update g rr (Glyph.mk 7)) rf Glyph.eos, X⟩ 1 :=
    ev_set' main rf Glyph.eos _ _
  have hbody : copyIntB2 t a b rr rf = .seq (.peek t rr) (.ite rr gMark (.set rf Glyph.eos)
      (.seq (.pop t rr) (.seq (.push a rr) (.seq (.push b rr) (.set rf Glyph.cons))))) := rfl
  refine ⟨⟨Function.update (Function.update g rr (Glyph.mk 7)) rf Glyph.eos, X⟩,
    3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]
    exact (Ev.seq h1 (Ev.iteT (by simp [Function.update_self, Work.Layout.gMark]) h2)).mono
      (by omega)
  · omega
  · simpa using ht
  · rfl
  · rfl
  · intro j; rfl
  · simp [Function.update_self]

private theorem copyIntB2_step_miss (main : Cmd) {t a b : Stk} (hta : t ≠ a) (htb : t ≠ b)
    (hab : a ≠ b) (rr rf : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    {h : Glyph} {Y : List Glyph}
    (ht : X t = h :: Y) (hh : h ≠ Glyph.mk 7) :
    ∃ s' n, Ev main (copyIntB2 t a b rr rf) ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk t = Y ∧ s'.stk a = h :: X a ∧ s'.stk b = h :: X b ∧
      (∀ j, j ≠ t → j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = Glyph.cons := by
  have h1 : Ev main (.peek t rr) ⟨g, X⟩ ⟨Function.update g rr h, X⟩ 1 := by
    have h := ev_peek' main t rr g X
    rw [ht, List.headD_cons] at h
    exact h
  have h2 : Ev main (.pop t rr) ⟨Function.update g rr h, X⟩
      ⟨Function.update (Function.update g rr h) rr h, Function.update X t Y⟩ 1 := by
    have h := ev_pop' main t rr (Function.update g rr h) X
    rw [ht, List.headD_cons, List.tail_cons] at h
    exact h
  have hbody : copyIntB2 t a b rr rf = .seq (.peek t rr) (.ite rr gMark (.set rf Glyph.eos)
      (.seq (.pop t rr) (.seq (.push a rr) (.seq (.push b rr) (.set rf Glyph.cons))))) := rfl
  refine ⟨⟨Function.update (Function.update (Function.update g rr h) rr h) rf Glyph.cons,
      Function.update
        (Function.update (Function.update X t Y) a
          ((Function.update (Function.update g rr h) rr h) rr :: Function.update X t Y a)) b
        ((Function.update (Function.update g rr h) rr h) rr ::
          Function.update (Function.update X t Y) a
            ((Function.update (Function.update g rr h) rr h) rr :: Function.update X t Y a) b)⟩,
    6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]
    exact (Ev.seq h1 (Ev.iteF (by simpa [Function.update_self, Work.Layout.gMark] using hh)
      (Ev.seq h2 (Ev.seq (ev_push' main a rr _ _)
        (Ev.seq (ev_push' main b rr _ _) (ev_set' main rf Glyph.cons _ _)))))).mono (by omega)
  · omega
  · simp [Function.update_self, Function.update_of_ne htb, Function.update_of_ne hta]
  · simp [Function.update_self, Function.update_of_ne hab, Function.update_of_ne (Ne.symm hta)]
  · simp [Function.update_self, Function.update_of_ne (Ne.symm hab), Function.update_of_ne htb.symm]
  · intro j hjt hja hjb
    simp [Function.update_self, Function.update_of_ne hjb, Function.update_of_ne hja,
      Function.update_of_ne hjt]
  · simp [Function.update_self]

theorem copyIntB2_loop (main : HvdH.Cmd) {t a b : HvdH.Stk} (hta : t ≠ a) (htb : t ≠ b)
    (hab : a ≠ b) (rr rf : HvdH.Reg) :
    ∀ (D DB : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      HvdH.Glyph.mk 7 ∉ D → g rf = HvdH.Glyph.cons → X t = D ++ HvdH.Glyph.mk 7 :: DB →
      ∃ s', Work.Layout.loopRuns main rf HvdH.Glyph.cons (Work.Layout.copyIntB2 t a b rr rf)
          (D.length + 1) ⟨g, X⟩ s' (7 * (D.length + 1)) ∧
        s'.stk t = HvdH.Glyph.mk 7 :: DB ∧ s'.stk a = D.reverse ++ X a ∧
        s'.stk b = D.reverse ++ X b ∧
        (∀ j, j ≠ t → j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = HvdH.Glyph.eos := by
  intro D
  induction D with
  | nil =>
      intro DB g X hD hg ht
      obtain ⟨s', n, hev, hn, ht', ha', hb', hfr', hrf⟩ :=
        copyIntB2_step_hit main (rr := rr) (rf := rf) g X (DB := DB) (by simpa using ht)
      refine ⟨s', ?_, ?_, ?_, ?_, ?_, hrf⟩
      · exact loopRuns.succ' hg (hev.mono hn) loopRuns.zero (by omega)
      · simpa using ht'
      · simpa using ha'
      · simpa using hb'
      · intro j _ _ _; exact hfr' j
  | cons d D' ih =>
      intro DB g X hD hg ht
      have hd : d ≠ Glyph.mk 7 := by intro h; exact hD (by rw [h]; exact List.mem_cons_self)
      have hD' : Glyph.mk 7 ∉ D' := fun h => hD (List.mem_cons_of_mem d h)
      obtain ⟨s₁, n₁, hev₁, hn₁, ht₁, ha₁, hb₁, hfr₁, hr₁⟩ :=
        copyIntB2_step_miss main (hta := hta) (htb := htb) (hab := hab) (rr := rr) (rf := rf)
          g X (h := d) (Y := D' ++ Glyph.mk 7 :: DB) (by simpa using ht) hd
      obtain ⟨s₂, hrun₂, ht₂, ha₂, hb₂, hfr₂, hr₂⟩ := ih DB s₁.reg s₁.stk hD' hr₁ ht₁
      refine ⟨s₂, ?_, ht₂, ?_, ?_, ?_, hr₂⟩
      · exact loopRuns.succ' hg (hev₁.mono hn₁) hrun₂ (by simp only [List.length_cons]; omega)
      · rw [ha₂, ha₁]
        simp [List.reverse_cons, List.append_assoc]
      · rw [hb₂, hb₁]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hjt hja hjb; rw [hfr₂ j hjt hja hjb, hfr₁ j hjt hja hjb]

end Work.Layout.AA
