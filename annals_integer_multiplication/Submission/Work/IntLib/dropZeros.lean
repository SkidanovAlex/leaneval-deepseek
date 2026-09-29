import Mathlib
import Submission.Work.IntLib.chunkDefs
import Submission.Work.Layout.Base

/-!
# `dropZerosProg`: popping the leading run of `bit false` glyphs

`Work.IntLib.dropZerosProg k r = peek k r; while reg r = bit false do (pop k r; peek k r)` pops the
maximal prefix of `Glyph.bit false` glyphs of the region of stack `k` which lies on top of a glyph
`M ≠ Glyph.bit false`.  The stop test uses the *peeked* glyph, so the first glyph which is not a
`false` bit is left on the stack (unlike `Work.IntLib.stripZeros`, which pops it and pushes it back).

`Work.IntLib.dropZeros` is the statement needed by the `chunk` word: starting on the push-order list
`l.reverse ++ M :: A` (so that the top of the stack is the *trailing* run of `l`), the whole word
(initial `peek` plus loop) ends with `(stripFalses l).reverse ++ M :: A` on the stack, touches no
other stack, and costs at most `3 * (l.length + 1) + 1` steps.
-/


namespace Work.IntLib

open HvdH

/-- The loop of `dropZerosProg`: from a state whose stack `k` holds `L ++ M :: A` (`M` not a
`false` bit) and whose register `r` holds the top glyph, the loop pops the leading `bit false`
glyphs and stops at the first glyph which is not a `false` bit, leaving it on top of the stack.

The cost is `≤ 3 * L.length + 1` (three steps per popped glyph: pop, peek and the loop test, plus
one final failing test); only stack `k` is modified. -/
theorem dropZeros_loop (main : HvdH.Cmd) (k : HvdH.Stk) (r : HvdH.Reg) {M : HvdH.Glyph}
    (hM : M ≠ HvdH.Glyph.bit false) :
    ∀ (L A : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph),
      X k = L ++ M :: A →
      g r = (X k).headD HvdH.Glyph.eos →
      ∃ (s' : HvdH.State) (n : ℕ),
        Work.Layout.Ev main
          (.loop r (HvdH.Glyph.bit false) (.seq (.pop k r) (.peek k r))) ⟨g, X⟩ s' n ∧
        n ≤ 3 * L.length + 1 ∧
        s'.stk k = L.dropWhile (fun h => h = HvdH.Glyph.bit false) ++ M :: A ∧
        (∀ j : HvdH.Stk, j ≠ k → s'.stk j = X j) := by
  intro L
  induction L with
  | nil =>
      intro A g X hX hg
      have hX' : X k = M :: A := by simpa using hX
      have hr : (⟨g, X⟩ : HvdH.State).reg r ≠ HvdH.Glyph.bit false := by
        have h1 : g r = M := by rw [hg, hX']; rfl
        show g r ≠ HvdH.Glyph.bit false
        rw [h1]
        exact hM
      refine ⟨⟨g, X⟩, 1, ?_, by simp, ?_, ?_⟩
      · exact Work.Layout.Ev.loopF hr
      · simpa using hX
      · intro j hj; rfl
  | cons h t ih =>
      intro A g X hX hg
      have hX' : X k = h :: (t ++ M :: A) := by simpa using hX
      have hreg : g r = h := by rw [hg, hX']; rfl
      by_cases hh : h = HvdH.Glyph.bit false
      · subst hh
        have hr : (⟨g, X⟩ : HvdH.State).reg r = HvdH.Glyph.bit false := hreg
        have hb1 : Work.Layout.Ev main (.pop k r) ⟨g, X⟩
            ⟨Function.update g r (HvdH.Glyph.bit false),
             Function.update X k (t ++ M :: A)⟩ 1 := by
          simpa [hX'] using Work.Layout.ev_pop' main k r g X
        have hb2 : Work.Layout.Ev main (.peek k r)
            ⟨Function.update g r (HvdH.Glyph.bit false), Function.update X k (t ++ M :: A)⟩
            ⟨Function.update (Function.update g r (HvdH.Glyph.bit false)) r
               (((Function.update X k (t ++ M :: A)) k).headD HvdH.Glyph.eos),
             Function.update X k (t ++ M :: A)⟩ 1 :=
          Work.Layout.ev_peek' main k r _ _
        have hbody : Work.Layout.Ev main (.seq (.pop k r) (.peek k r)) ⟨g, X⟩
            ⟨Function.update (Function.update g r (HvdH.Glyph.bit false)) r
               (((Function.update X k (t ++ M :: A)) k).headD HvdH.Glyph.eos),
             Function.update X k (t ++ M :: A)⟩ 2 := by
          simpa using Work.Layout.Ev.seq hb1 hb2
        have hX1 : (Function.update X k (t ++ M :: A)) k = t ++ M :: A := by simp
        have hg1 : (Function.update (Function.update g r (HvdH.Glyph.bit false)) r
              (((Function.update X k (t ++ M :: A)) k).headD HvdH.Glyph.eos)) r
            = (((Function.update X k (t ++ M :: A)) k).headD HvdH.Glyph.eos) := by simp
        obtain ⟨s', n', hloop, hn', hstk', hfr⟩ := ih A
          (Function.update (Function.update g r (HvdH.Glyph.bit false)) r
             (((Function.update X k (t ++ M :: A)) k).headD HvdH.Glyph.eos))
          (Function.update X k (t ++ M :: A)) hX1 hg1
        refine ⟨s', 2 + n' + 1, ?_, ?_, ?_, ?_⟩
        · exact Work.Layout.Ev.loopT hr hbody hloop
        · have hlen : (HvdH.Glyph.bit false :: t).length = t.length + 1 := List.length_cons
          have hn'' : n' ≤ 3 * t.length + 1 := hn'
          rw [hlen]; omega
        · have hdw : (HvdH.Glyph.bit false :: t).dropWhile (fun h => h = HvdH.Glyph.bit false)
              = t.dropWhile (fun h => h = HvdH.Glyph.bit false) :=
            List.dropWhile_cons_of_pos (by rfl)
          simpa [hdw] using hstk'
        · intro j hj
          simpa only [Function.update_of_ne hj] using hfr j hj
      · refine ⟨⟨g, X⟩, 1, ?_, by simp, ?_, ?_⟩
        · have hr : (⟨g, X⟩ : HvdH.State).reg r ≠ HvdH.Glyph.bit false := by
            show g r ≠ HvdH.Glyph.bit false
            rw [hreg]; exact hh
          exact Work.Layout.Ev.loopF hr
        · have hdw : (h :: t).dropWhile (fun h => h = HvdH.Glyph.bit false) = h :: t :=
            List.dropWhile_cons_of_neg (by simpa using hh)
          simpa [hdw] using hX'
        · intro j hj; rfl

theorem dropZeros (main : HvdH.Cmd) (k : HvdH.Stk) (r : HvdH.Reg) {M : HvdH.Glyph}
    (hM : M ≠ HvdH.Glyph.bit false) :
    ∀ (l : List HvdH.Glyph) (A : List HvdH.Glyph) (g : HvdH.Reg → HvdH.Glyph)
      (X : HvdH.Stk → List HvdH.Glyph),
      X k = l.reverse ++ M :: A →
      ∃ (s' : HvdH.State) (n : ℕ),
        Work.Layout.Ev main (Work.IntLib.dropZerosProg k r) ⟨g, X⟩ s' n ∧
        n ≤ 3 * (l.length + 1) + 1 ∧
        s'.stk k = (Work.IntLib.stripFalses l).reverse ++ M :: A ∧
        (∀ j : HvdH.Stk, j ≠ k → s'.stk j = X j) := by
  intro l A g X hX
  have hpeek : Work.Layout.Ev main (.peek k r) ⟨g, X⟩
      ⟨Function.update g r ((X k).headD HvdH.Glyph.eos), X⟩ 1 :=
    Work.Layout.ev_peek' main k r g X
  have hg1 : (Function.update g r ((X k).headD HvdH.Glyph.eos)) r
      = (X k).headD HvdH.Glyph.eos := by simp
  obtain ⟨s', n', hloop, hn', hstk', hfr⟩ :=
    dropZeros_loop main k r hM (l.reverse) A
      (Function.update g r ((X k).headD HvdH.Glyph.eos)) X hX hg1
  refine ⟨s', 1 + n', ?_, ?_, ?_, ?_⟩
  · simpa only [Work.IntLib.dropZerosProg] using Work.Layout.Ev.seq hpeek hloop
  · have hn'' : n' ≤ 3 * l.length + 1 := by simpa using hn'
    omega
  · have hstrip : (Work.IntLib.stripFalses l).reverse
        = l.reverse.dropWhile (fun h => h = HvdH.Glyph.bit false) := by
      simp [Work.IntLib.stripFalses]
    rw [hstrip]
    exact hstk'
  · intro j hj; exact hfr j hj

end Work.IntLib
