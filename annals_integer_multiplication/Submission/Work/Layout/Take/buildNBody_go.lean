import Mathlib
import Submission.Work.Layout.Take.Defs
import Submission.Work.Layout.mvVal_ev_full

/-!
# One iteration of the counter-driven rebuild loop (`buildNBody`)

`Work.Layout.buildNBody c b` is the body of `buildNProg c b`
(`Submission/Work/Layout/Take/Defs.lean`): it peeks the counter stack `c`; if the top there is a
unary unit `gU` it pops it, moves the top value of the carrier stack `b` onto the value stack `0`
(in front of a freshly pushed `Glyph.cons`), and sets the loop register `rG` back to `gCont_x` so
that the loop keeps running.

This file proves that single step, with its cost `16 * (vsz v + 1) + 6`, and with the frame
conditions (`mvVal_ev_full` is the version of `mvVal` that also restores its own scratch stacks
`sX`, `sY`, so every stack other than `c`, `b`, `0` is left untouched).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Layout.Take

open HvdH

theorem buildNBody_go (main : HvdH.Cmd) (c b : HvdH.Stk) (hc0 : c ≠ 0) (hb0 : b ≠ 0)
    (hbc : c ≠ b) (hbX : b ≠ Work.Layout.sX) (hbY : b ≠ Work.Layout.sY)
    (hcX : c ≠ Work.Layout.sX) (hcY : c ≠ Work.Layout.sY)
    {v : HvdH.Val} {C B A : List HvdH.Glyph} {g : HvdH.Reg → HvdH.Glyph}
    {X : HvdH.Stk → List HvdH.Glyph}
    (hc : X c = Work.Layout.gU :: C) (hb : X b = v.enc ++ B) (h0 : X 0 = A) :
    ∃ s' n, Work.Layout.Ev main (Work.Layout.buildNBody c b) ⟨g, X⟩ s' n ∧
      n ≤ 16 * (HvdH.vsz v + 1) + 6 ∧
      s'.stk c = C ∧ s'.stk b = B ∧ s'.stk 0 = HvdH.Glyph.cons :: (v.enc ++ A) ∧
      s'.reg Work.Layout.rG = Work.Layout.gCont_x ∧
      s'.stk Work.Layout.sX = X Work.Layout.sX ∧ s'.stk Work.Layout.sY = X Work.Layout.sY ∧
      (∀ j, j ≠ c → j ≠ b → j ≠ 0 → j ≠ Work.Layout.sX → j ≠ Work.Layout.sY →
        s'.stk j = X j) := by
  -- the head of stack `c` is the unary unit; the pop reads exactly that
  have hhead : (X c).headD Glyph.eos = Work.Layout.gU := by rw [hc]; rfl
  have htail : (X c).tail = C := by rw [hc]; rfl
  have hreg : (Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos)) Work.Layout.rE_x
      = Work.Layout.gU := by rw [Function.update_self, hhead]
  -- `peek c rE_x`
  have hpeek : Ev main (.peek c Work.Layout.rE_x) ⟨g, X⟩
      ⟨Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos), X⟩ 1 :=
    ev_peek' main c Work.Layout.rE_x g X
  -- `pop c rE_x`
  have hpop : Ev main (.pop c Work.Layout.rE_x)
      ⟨Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos))
          Work.Layout.rE_x ((X c).headD Glyph.eos),
        Function.update X c (X c).tail⟩ 1 :=
    ev_pop' main c Work.Layout.rE_x _ X
  -- the state after the `pop`, and the hypotheses the `mvVal` needs
  have hb2 : (Function.update X c (X c).tail) b = v.enc ++ B := by
    rw [htail, Function.update_of_ne hbc.symm C X]; exact hb
  have h02 : (Function.update X c (X c).tail) 0 = A := by
    rw [htail, Function.update_of_ne hc0.symm C X]; exact h0
  -- the value move
  obtain ⟨s₁, n₁, he₁, hn₁, hA, hB, hXc, hYc, hfr⟩ :=
    mvVal_ev_full (main := main) (a := b) (b := (0 : HvdH.Stk))
      (c := Work.Layout.sX) (d := Work.Layout.sY)
      (g := Function.update (Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos))
        Work.Layout.rE_x ((X c).headD Glyph.eos))
      (X := Function.update X c (X c).tail) (v := v) (A := B) (B := A)
      hb0 hbX hbY (by decide) (by decide) (by decide) hb2 h02
  have hc₁ : s₁.stk c = C := by
    rw [hfr c hbc hc0 hcX hcY, Function.update_self, htail]
  have hsX₁ : s₁.stk Work.Layout.sX = X Work.Layout.sX := by
    rw [hXc, Function.update_of_ne hcX.symm]
  have hsY₁ : s₁.stk Work.Layout.sY = X Work.Layout.sY := by
    rw [hYc, Function.update_of_ne hcY.symm]
  -- then `set rE_x Glyph.cons ;; push 0 rE_x ;; set rG gCont_x`
  have hset : Ev main (.set Work.Layout.rE_x Glyph.cons) s₁
      ⟨Function.update s₁.reg Work.Layout.rE_x Glyph.cons, s₁.stk⟩ 1 :=
    ev_set' main Work.Layout.rE_x Glyph.cons s₁.reg s₁.stk
  have hpush : Ev main (.push (0 : HvdH.Stk) Work.Layout.rE_x)
      ⟨Function.update s₁.reg Work.Layout.rE_x Glyph.cons, s₁.stk⟩
      ⟨Function.update s₁.reg Work.Layout.rE_x Glyph.cons,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩ 1 := by
    have h := ev_push' main (0 : HvdH.Stk) Work.Layout.rE_x
      (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) s₁.stk
    rwa [Function.update_self] at h
  have hsetg : Ev main (.set Work.Layout.rG Work.Layout.gCont_x)
      ⟨Function.update s₁.reg Work.Layout.rE_x Glyph.cons,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩
      ⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
          Work.Layout.gCont_x,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩ 1 :=
    ev_set' main Work.Layout.rG Work.Layout.gCont_x _ _
  have htail3 : Ev main
      (.seq (.set Work.Layout.rE_x Glyph.cons)
        (.seq (.push (0 : HvdH.Stk) Work.Layout.rE_x) (.set Work.Layout.rG Work.Layout.gCont_x)))
      s₁
      ⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
          Work.Layout.gCont_x,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩ 3 :=
    Ev.seq' hset (Ev.seq' hpush hsetg (by rfl)) (by rfl)
  -- the `then` branch of the `ite`
  have hbranch : Ev main
      (.seq (.pop c Work.Layout.rE_x)
        (.seq (mvVal b (0 : HvdH.Stk) Work.Layout.sX Work.Layout.sY)
          (.seq (.set Work.Layout.rE_x Glyph.cons)
            (.seq (.push (0 : HvdH.Stk) Work.Layout.rE_x)
              (.set Work.Layout.rG Work.Layout.gCont_x)))))
      ⟨Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
          Work.Layout.gCont_x,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩
      (1 + (n₁ + 3)) :=
    Ev.seq' hpop (Ev.seq' he₁ htail3 (by rfl)) (by rfl)
  have hite : Ev main
      (.ite Work.Layout.rE_x Work.Layout.gU
        (.seq (.pop c Work.Layout.rE_x)
          (.seq (mvVal b (0 : HvdH.Stk) Work.Layout.sX Work.Layout.sY)
            (.seq (.set Work.Layout.rE_x Glyph.cons)
              (.seq (.push (0 : HvdH.Stk) Work.Layout.rE_x)
                (.set Work.Layout.rG Work.Layout.gCont_x)))))
        (.set Work.Layout.rG Glyph.eos))
      ⟨Function.update g Work.Layout.rE_x ((X c).headD Glyph.eos), X⟩
      ⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
          Work.Layout.gCont_x,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩
      (1 + (n₁ + 3) + 1) :=
    Ev.iteT hreg hbranch
  have hbody : Ev main
      (.seq (.peek c Work.Layout.rE_x)
        (.ite Work.Layout.rE_x Work.Layout.gU
          (.seq (.pop c Work.Layout.rE_x)
            (.seq (mvVal b (0 : HvdH.Stk) Work.Layout.sX Work.Layout.sY)
              (.seq (.set Work.Layout.rE_x Glyph.cons)
                (.seq (.push (0 : HvdH.Stk) Work.Layout.rE_x)
                  (.set Work.Layout.rG Work.Layout.gCont_x)))))
          (.set Work.Layout.rG Glyph.eos))) ⟨g, X⟩
      ⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
          Work.Layout.gCont_x,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩
      (1 + (1 + (n₁ + 3) + 1)) :=
    Ev.seq' hpeek hite (by rfl)
  have hmain : Ev main (Work.Layout.buildNBody c b) ⟨g, X⟩
      ⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
          Work.Layout.gCont_x,
        Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩
      (1 + (1 + (n₁ + 3) + 1)) := by
    unfold Work.Layout.buildNBody
    exact hbody
  refine ⟨⟨Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
      Work.Layout.gCont_x,
      Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))⟩,
    1 + (1 + (n₁ + 3) + 1), hmain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · show Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk)) c = C
    rw [Function.update_of_ne hc0, hc₁]
  · show Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk)) b = B
    rw [Function.update_of_ne hb0, hA]
  · show Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk)) (0 : HvdH.Stk)
        = Glyph.cons :: (v.enc ++ A)
    rw [Function.update_self, hB]
  · show Function.update (Function.update s₁.reg Work.Layout.rE_x Glyph.cons) Work.Layout.rG
        Work.Layout.gCont_x Work.Layout.rG = Work.Layout.gCont_x
    rw [Function.update_self]
  · show Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))
        Work.Layout.sX = X Work.Layout.sX
    rw [Function.update_of_ne (by decide : Work.Layout.sX ≠ (0 : HvdH.Stk)), hsX₁]
  · show Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk))
        Work.Layout.sY = X Work.Layout.sY
    rw [Function.update_of_ne (by decide : Work.Layout.sY ≠ (0 : HvdH.Stk)), hsY₁]
  · intro j hjc hjb hj0 hjX hjY
    show Function.update s₁.stk (0 : HvdH.Stk) (Glyph.cons :: s₁.stk (0 : HvdH.Stk)) j = X j
    rw [Function.update_of_ne hj0, hfr j hjb hj0 hjX hjY,
      Function.update_of_ne hjc]

end Work.Layout.Take
