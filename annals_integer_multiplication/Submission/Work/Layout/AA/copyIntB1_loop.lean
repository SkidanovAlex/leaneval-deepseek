import Mathlib
import Submission.Work.Layout.AA.Defs

/-!
# `copyIntB1`: the first loop of `copyIntTo`

`Work.Layout.copyIntB1 a t rr rf` is the body of the first loop of `copyIntTo`: it pops one glyph
from stack `a`, pushes it onto stack `t`, and sets the flag register `rf` to `Glyph.eos` when the
popped glyph is the integer terminator `Glyph.iend` (so that the loop stops there) and to
`Glyph.cons` otherwise (so that the loop goes on).

Starting from `X a = D ++ Glyph.iend :: A` where `Glyph.iend` does not occur in `D`, the loop
therefore performs exactly `D.length + 1` iterations: the block `D` is moved onto `t` (hence
reversed) and then the terminator `Glyph.iend` follows it.  The final stack `a` is `A`, and stack
`t` is `Glyph.iend :: D.reverse ++ X t`; no other stack is touched.  Cost: `4` steps per iteration
plus `1` for the loop test, i.e. `5 * (D.length + 1)`.

* `copyIntB1_step`: one iteration of the body;
* `copyIntB1_loop`: the whole loop (the statement of the task).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Layout.AA

open HvdH

/-- One iteration of the `copyIntB1` loop: pop the top glyph `d` of stack `a`, push it onto stack
`t`, and set the flag register to `Glyph.eos` (stop) if `d = Glyph.iend`, to `Glyph.cons`
(continue) otherwise.  Cost: `pop` + `push` + (`ite` test + `set`) = `4`. -/
theorem copyIntB1_step (main : HvdH.Cmd) {a t : HvdH.Stk} (hat : a ≠ t)
    (rr rf : HvdH.Reg) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
    {d : HvdH.Glyph} {A : List HvdH.Glyph} (ha : X a = d :: A) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.copyIntB1 a t rr rf) ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk a = A ∧ s'.stk t = d :: X t ∧
      (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) ∧
      s'.reg rf = (if d = HvdH.Glyph.iend then HvdH.Glyph.eos else HvdH.Glyph.cons) := by
  have h1 : Work.Layout.Ev main (.pop a rr) ⟨g, X⟩
      ⟨Function.update g rr d, Function.update X a A⟩ 1 := by
    have h := Work.Layout.ev_pop' main a rr g X
    rw [ha, List.headD_cons, List.tail_cons] at h
    exact h
  have h2 : Work.Layout.Ev main (.push t rr) ⟨Function.update g rr d, Function.update X a A⟩
      ⟨Function.update g rr d,
        Function.update (Function.update X a A) t (d :: Function.update X a A t)⟩ 1 := by
    have h := Work.Layout.ev_push' main t rr (Function.update g rr d) (Function.update X a A)
    simpa using h
  have h3 : Work.Layout.Ev main (.ite rr Glyph.iend (.set rf Glyph.eos) (.set rf Glyph.cons))
      ⟨Function.update g rr d, Function.update (Function.update X a A) t
        (d :: Function.update X a A t)⟩
      ⟨Function.update (Function.update g rr d) rf
          (if d = Glyph.iend then Glyph.eos else Glyph.cons),
        Function.update (Function.update X a A) t (d :: Function.update X a A t)⟩ 2 := by
    split_ifs with hde
    · exact Work.Layout.Ev.iteT (by simp only [Function.update_self]; exact hde)
        (Work.Layout.ev_set' main rf Glyph.eos _ _)
    · exact Work.Layout.Ev.iteF (by simp only [Function.update_self]; exact hde)
        (Work.Layout.ev_set' main rf Glyph.cons _ _)
  have h23 : Work.Layout.Ev main (.seq (.push t rr)
      (.ite rr Glyph.iend (.set rf Glyph.eos) (.set rf Glyph.cons)))
      ⟨Function.update g rr d, Function.update X a A⟩
      ⟨Function.update (Function.update g rr d) rf
          (if d = Glyph.iend then Glyph.eos else Glyph.cons),
        Function.update (Function.update X a A) t (d :: Function.update X a A t)⟩ 3 :=
    Work.Layout.Ev.seq' h2 h3 (by omega)
  have hbody : Work.Layout.copyIntB1 a t rr rf = .seq (.pop a rr)
      (.seq (.push t rr) (.ite rr Glyph.iend (.set rf Glyph.eos) (.set rf Glyph.cons))) := rfl
  refine ⟨⟨Function.update (Function.update g rr d) rf
      (if d = Glyph.iend then Glyph.eos else Glyph.cons),
      Function.update (Function.update X a A) t (d :: Function.update X a A t)⟩, 4,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbody]; exact Work.Layout.Ev.seq' h1 h23 (by omega)
  · omega
  · rw [stk_mk, Function.update_of_ne hat, Function.update_self]
  · rw [stk_mk, Function.update_self, Function.update_of_ne hat.symm]
  · intro j hja hjt
    rw [stk_mk, Function.update_of_ne hjt, Function.update_of_ne hja]
  · rw [reg_mk, Function.update_self]

theorem copyIntB1_loop (main : HvdH.Cmd) {a t : HvdH.Stk} (hat : a ≠ t) (rr rf : HvdH.Reg) :
    ∀ (D A : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      HvdH.Glyph.iend ∉ D → g rf = HvdH.Glyph.cons → X a = D ++ HvdH.Glyph.iend :: A →
      ∃ s', Work.Layout.loopRuns main rf HvdH.Glyph.cons (Work.Layout.copyIntB1 a t rr rf)
          (D.length + 1) ⟨g, X⟩ s' (5 * (D.length + 1)) ∧
        s'.stk a = A ∧ s'.stk t = HvdH.Glyph.iend :: D.reverse ++ X t ∧
        (∀ j, j ≠ a → j ≠ t → s'.stk j = X j) ∧ s'.reg rf = HvdH.Glyph.eos := by
  intro D
  induction D with
  | nil =>
      intro A g X _ hg hX
      simp only [List.nil_append] at hX
      obtain ⟨s', n, hev, hn, ha', ht', hfr', hrf'⟩ :=
        copyIntB1_step (main := main) (a := a) (t := t) hat rr rf g X hX
      refine ⟨s', ?_, ha', ?_, ?_, ?_⟩
      · simpa using (Work.Layout.loopRuns.one hg (hev.mono hn))
      · simpa using ht'
      · intro j hja hjt; exact hfr' j hja hjt
      · simpa using hrf'
  | cons d D ih =>
      intro A g X hD hg hX
      rw [List.mem_cons, not_or] at hD
      have hdne : d ≠ Glyph.iend := fun h => hD.1 h.symm
      have hD' : Glyph.iend ∉ D := hD.2
      obtain ⟨s₁, n₁, hev₁, hn₁, ha₁, ht₁, hfr₁, hr₁⟩ :=
        copyIntB1_step (main := main) (a := a) (t := t) hat rr rf g X hX
      have hrc : s₁.reg rf = Glyph.cons := by rw [hr₁]; simp [hdne]
      obtain ⟨s₂, hrun₂, ha₂, ht₂, hfr₂, hr₂⟩ := ih A s₁.reg s₁.stk hD' hrc ha₁
      have hcat := Work.Layout.loopRuns.concat (D.length + 1)
        (Work.Layout.loopRuns.one hg (hev₁.mono hn₁)) hrun₂
      refine ⟨s₂, ?_, ha₂, ?_, ?_, hr₂⟩
      · refine Work.Layout.loopRuns.congr ?_ ?_ hcat
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
      · rw [ht₂, ht₁]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      · intro j hja hjt
        rw [hfr₂ j hja hjt, hfr₁ j hja hjt]

end Work.Layout.AA
