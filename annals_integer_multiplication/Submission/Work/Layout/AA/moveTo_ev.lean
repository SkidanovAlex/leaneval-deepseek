import Mathlib
import Submission.Work.Layout.AA.Defs

/-!
# `moveTo`: moving the glyphs above the boundary marker of stack `a` onto stack `b`

`Work.Layout.moveTo a b rr rf` runs `Work.Layout.moveToBody a b rr rf` in a loop; one iteration of the
body peeks the top of stack `a`:

* if the peeked glyph is the boundary marker `Glyph.mk 7`, it takes the `then` branch, which sets the
  flag register `rf` to `Glyph.eos` — stopping the loop — and leaves every stack untouched;
* otherwise it takes the `else` branch, which pops the glyph from `a`, pushes it onto `b` and sets
  `rf` to `Glyph.cons` so that the loop continues.

Hence, starting from a state whose stack `a` is `D ++ Glyph.mk 7 :: B` (where the marker does not
occur in `D`, so that the loop stops exactly at the marker), `moveTo` ends with stack `a` equal to
`Glyph.mk 7 :: B` and stack `b` equal to `D.reverse ++ X b`: the block `D` has been *reversed* while
being moved.  No other stack is touched.

* `moveToBody_hit` / `moveToBody_miss`: one iteration of the loop (marker on top / not on top);
* `moveTo_loop`: the iteration of the body over the whole block `D`;
* `moveTo_ev`: the program `moveTo` (statement of the task).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

/-- One iteration of the `moveTo` loop when the top glyph of `a` is the boundary marker: the body
peeks, takes the `then` branch, sets the flag register to `Glyph.eos` (so the loop stops) and leaves
both stacks unchanged.  Cost: `peek` + `ite` + `set` = `3`. -/
private theorem moveToBody_hit (main : Cmd) {a b : Stk} {rr rf : Reg}
    (g : Reg → Glyph) (X : Stk → List Glyph) (B : List Glyph)
    (ha : X a = Glyph.mk 7 :: B) :
    ∃ s' n, Ev main (moveToBody a b rr rf) ⟨g, X⟩ s' n ∧ n ≤ 3 ∧
      s'.stk a = Glyph.mk 7 :: B ∧ s'.stk b = X b ∧
      (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = Glyph.eos := by
  have h1 : Ev main (.peek a rr) ⟨g, X⟩ ⟨Function.update g rr (Glyph.mk 7), X⟩ 1 := by
    have h := ev_peek' main a rr g X
    rw [ha, List.headD_cons] at h
    exact h
  have h2 : Ev main (.ite rr (Glyph.mk 7) (.set rf Glyph.eos)
      (.seq (.pop a rr) (.seq (.push b rr) (.set rf Glyph.cons))))
      ⟨Function.update g rr (Glyph.mk 7), X⟩
      ⟨Function.update (Function.update g rr (Glyph.mk 7)) rf Glyph.eos, X⟩ 2 :=
    Ev.iteT (by simp) (ev_set' main rf Glyph.eos _ X)
  have hbody : moveToBody a b rr rf = .seq (.peek a rr) (.ite rr (Glyph.mk 7)
      (.set rf Glyph.eos) (.seq (.pop a rr) (.seq (.push b rr) (.set rf Glyph.cons)))) := rfl
  refine ⟨⟨Function.update (Function.update g rr (Glyph.mk 7)) rf Glyph.eos, X⟩, 3,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]; exact Ev.seq' h1 h2 (by omega)
  · omega
  · rw [stk_mk, ha]
  · rw [stk_mk]
  · intro j _ _; rw [stk_mk]
  · rw [reg_mk]; simp

/-- One iteration of the `moveTo` loop when the top glyph `h` of `a` is *not* the boundary marker:
the body peeks, takes the `else` branch, and thereby pops `h` from `a` and pushes it onto `b`, setting
the flag register to `Glyph.cons` (so the loop continues).  Cost: `peek` + `ite` + `pop` + `push` +
`set` = `5`. -/
private theorem moveToBody_miss (main : Cmd) {a b : Stk} (hab : a ≠ b) {rr rf : Reg}
    (g : Reg → Glyph) (X : Stk → List Glyph) {h : Glyph} {A C : List Glyph}
    (ha : X a = h :: A) (hh : h ≠ Glyph.mk 7) (hb : X b = C) :
    ∃ s' n, Ev main (moveToBody a b rr rf) ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk a = A ∧ s'.stk b = h :: C ∧
      (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = Glyph.cons := by
  have h1 : Ev main (.peek a rr) ⟨g, X⟩ ⟨Function.update g rr h, X⟩ 1 := by
    have h := ev_peek' main a rr g X
    rw [ha, List.headD_cons] at h
    exact h
  have hp : Ev main (.pop a rr) ⟨Function.update g rr h, X⟩
      ⟨Function.update g rr h, Function.update X a A⟩ 1 := by
    have h := ev_pop' main a rr (Function.update g rr h) X
    rw [ha, List.headD_cons, List.tail_cons] at h
    simpa using h
  have hq : Ev main (.push b rr) ⟨Function.update g rr h, Function.update X a A⟩
      ⟨Function.update g rr h,
        Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩ 1 := by
    have h := ev_push' main b rr (Function.update g rr h) (Function.update X a A)
    simpa using h
  have hr : Ev main (.set rf Glyph.cons)
      ⟨Function.update g rr h, Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩
      ⟨Function.update (Function.update g rr h) rf Glyph.cons,
        Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩ 1 :=
    ev_set' main rf Glyph.cons _ _
  have h23a : Ev main (.seq (.push b rr) (.set rf Glyph.cons))
      ⟨Function.update g rr h, Function.update X a A⟩
      ⟨Function.update (Function.update g rr h) rf Glyph.cons,
        Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩ 2 :=
    Ev.seq' hq hr (by omega)
  have h23 : Ev main (.seq (.pop a rr) (.seq (.push b rr) (.set rf Glyph.cons)))
      ⟨Function.update g rr h, X⟩
      ⟨Function.update (Function.update g rr h) rf Glyph.cons,
        Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩ 3 :=
    Ev.seq' hp h23a (by omega)
  have h2 : Ev main (.ite rr (Glyph.mk 7) (.set rf Glyph.eos)
      (.seq (.pop a rr) (.seq (.push b rr) (.set rf Glyph.cons))))
      ⟨Function.update g rr h, X⟩
      ⟨Function.update (Function.update g rr h) rf Glyph.cons,
        Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩ 4 :=
    Ev.iteF (by simpa using hh) h23
  have hbody : moveToBody a b rr rf = .seq (.peek a rr) (.ite rr (Glyph.mk 7)
      (.set rf Glyph.eos) (.seq (.pop a rr) (.seq (.push b rr) (.set rf Glyph.cons)))) := rfl
  refine ⟨⟨Function.update (Function.update g rr h) rf Glyph.cons,
      Function.update (Function.update X a A) b (h :: Function.update X a A b)⟩, 5,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]; exact Ev.seq' h1 h2 (by omega)
  · omega
  · rw [stk_mk, Function.update_of_ne hab, Function.update_self]
  · rw [stk_mk, Function.update_self, Function.update_of_ne hab.symm, hb]
  · intro j hja hjb
    rw [stk_mk, Function.update_of_ne hjb, Function.update_of_ne hja]
  · rw [reg_mk]; simp

/-- Iterating `moveToBody` over the block `D`: from `X a = D ++ gMark :: B`, `D.length + 1` iterations
of the body (the last one hitting the marker, which stops the loop) move `D` to `b` reversed, with
total cost `6 * D.length + 4` (including the `D.length + 1` loop tests). -/
private theorem moveTo_loop (main : Cmd) {a b : Stk} (hab : a ≠ b) (rr rf : Reg) :
    ∀ (D B C : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      Glyph.mk 7 ∉ D → X a = D ++ Glyph.mk 7 :: B → X b = C → g rf = Glyph.cons →
      ∃ s', loopRuns main rf Glyph.cons (moveToBody a b rr rf) (D.length + 1) ⟨g, X⟩ s'
          (6 * D.length + 4) ∧
        s'.stk a = Glyph.mk 7 :: B ∧ s'.stk b = D.reverse ++ C ∧
        (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) ∧ s'.reg rf = Glyph.eos := by
  intro D
  induction D with
  | nil =>
      intro B C g X hD ha hb hg
      simp only [List.nil_append] at ha
      obtain ⟨s', n, hev, hn, ha', hb', hfr', hrf⟩ :=
        moveToBody_hit (main := main) (a := a) (b := b) (rr := rr) (rf := rf) g X B ha
      refine ⟨s', loopRuns.one hg (hev.mono hn), ha', ?_, ?_, hrf⟩
      · rw [hb']; exact hb
      · intro j hja hjb; exact hfr' j hja hjb
  | cons d D' ih =>
      intro B C g X hD ha hb hg
      rw [List.mem_cons, not_or] at hD
      have hd : d ≠ Glyph.mk 7 := fun h => hD.1 h.symm
      have hD' : Glyph.mk 7 ∉ D' := hD.2
      have ha' : X a = d :: (D' ++ Glyph.mk 7 :: B) := ha
      obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, hb₁, hfr₁, hr₁⟩ :=
        moveToBody_miss (main := main) (a := a) (b := b) (rr := rr) (rf := rf) hab g X ha' hd hb
      obtain ⟨s₂, hrun₂, ha₂, hb₂, hfr₂, hr₂⟩ := ih B (d :: C) s₁.reg s₁.stk hD' ha₁ hb₁ hr₁
      refine ⟨s₂, loopRuns.succ' hg (hev₁.mono hn₁) hrun₂ ?_, ha₂, ?_, ?_, hr₂⟩
      · simp only [List.length_cons]; omega
      · rw [hb₂]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      · intro j hja hjb
        rw [hfr₂ j hja hjb, hfr₁ j hja hjb]

theorem moveTo_ev (main : HvdH.Cmd) (a b : HvdH.Stk) (rr rf : HvdH.Reg) (hrr : rr ≠ rf)
    (hab : a ≠ b) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    (D B : List HvdH.Glyph) (hD : HvdH.Glyph.mk 7 ∉ D)
    (ha : X a = D ++ HvdH.Glyph.mk 7 :: B) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.moveTo a b rr rf) ⟨g, X⟩ s' n ∧
      n ≤ 6 * D.length + 8 ∧ s'.stk a = HvdH.Glyph.mk 7 :: B ∧ s'.stk b = D.reverse ++ X b ∧
      (∀ j, j ≠ a → j ≠ b → s'.stk j = X j) := by
  obtain ⟨s₁, hrun, ha₁, hb₁, hfr₁, hr₁⟩ :=
    moveTo_loop (main := main) (a := a) (b := b) (hab := hab) (rr := rr) (rf := rf) D B (X b)
      (Function.update g rf Glyph.cons) X hD ha rfl (by simp)
  have hloop : Ev main (.loop rf Glyph.cons (moveToBody a b rr rf))
      ⟨Function.update g rf Glyph.cons, X⟩ s₁ (6 * D.length + 4 + 1) :=
    loopRuns.eval hrun (by rw [hr₁]; decide)
  have h0 : Ev main (.set rf Glyph.cons) ⟨g, X⟩ ⟨Function.update g rf Glyph.cons, X⟩ 1 :=
    ev_set' main rf Glyph.cons g X
  have hmain : Ev main (moveTo a b rr rf) ⟨g, X⟩ s₁ (6 * D.length + 6) := by
    have hd : moveTo a b rr rf
        = .seq (.set rf Glyph.cons) (.loop rf Glyph.cons (moveToBody a b rr rf)) := rfl
    rw [hd]
    exact Ev.seq' h0 hloop (by omega)
  exact ⟨s₁, 6 * D.length + 6, hmain, by omega, ha₁, hb₁, hfr₁⟩

end Work.Layout.AA
